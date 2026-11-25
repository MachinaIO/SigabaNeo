/-
UNTRUSTED. The syntactic filter of the DAG's verifier (docs/GITHUB_PLATFORM.md, "Defense in depth").

Lean runs code while it elaborates a file (`#eval`, `run_cmd`, `run_tac`, custom elaborators, …).
`lintFile` reads a DAG file *without elaborating it*: it parses each command and rejects any that
can run code at elaboration time or extend the syntax. The only commands it elaborates are those
that change how later commands parse and run no code of the file: `open`, `namespace`, `section`,
`end`. Since no DAG file may declare syntax, every DAG file is parsed with the syntax of the core,
std, Mathlib and cslib-frontier only.

The caller runs this in a Lean process that imports the file's own imports (already checked
against the DAG's allowed roots, and built), so that their environment extensions exist while the
file is parsed.

The list cannot be complete: the sandbox around the build is the real boundary. The filter only
makes the common ways fail early and visibly.
-/
import Lean

open Lean Elab Frontend

namespace SigabaNeo.Platform.Lint

/-- Keywords (atoms) whose syntax declares syntax or elaborators, or runs code. -/
def forbiddenKeywords : List String :=
  ["syntax", "macro", "macro_rules", "elab", "elab_rules", "notation", "notation3", "infix",
   "infixl", "infixr", "prefix", "postfix", "declare_syntax_cat", "initialize",
   "builtin_initialize", "run_cmd", "run_elab", "run_meta", "run_tac", "by_elab", "native_decide",
   "simproc", "dsimproc", "builtin_simproc", "builtin_dsimproc", "simproc_decl", "dsimproc_decl",
   "register_simp_attr", "register_option", "register_builtin_option", "register_label_attr",
   "declare_config_elab", "binder_predicate", "declare_simp_like_tactic", "elab_stx_quot",
   "unsafe", "partial", "implemented_by", "extern", "dsimproc_pattern", "simproc_pattern",
   "cbv_simproc", "cbv_simproc_pattern"]

/-- Attributes that register code to run later (elaborators, extensions, initializers). -/
def forbiddenAttributes : List String :=
  ["command_elab", "term_elab", "tactic", "macro", "delab", "app_unexpander", "app_delab", "init",
   "implemented_by", "extern", "export", "csimp", "simproc", "sevalproc", "cbv_simproc",
   "norm_num", "positivity", "env_linter", "command_parser", "term_parser", "tactic_parser",
   "combinator_formatter", "combinator_parenthesizer", "category_parenthesizer",
   "run_builtin_parser_attribute_hooks", "run_parser_attribute_hooks", "code_action_provider",
   "command_code_action", "hole_code_action", "tactic_code_action", "widget_module",
   "server_rpc_method", "missing_docs_handler", "incremental", "inherit_doc_from", "attr_parser",
   "key_parser", "aesop"]

/-- `#` commands that only display information. Every other `#…` command is rejected. -/
def allowedHashCommands : List String := ["#check", "#print", "#exit", "#guard_msgs", "#synth"]

/-- Prefixes of the options a DAG file may set. -/
def allowedOptionPrefixes : List String :=
  ["maxHeartbeats", "maxRecDepth", "autoImplicit", "relaxedAutoImplicit", "linter.", "pp.",
   "synthInstance.", "exponentiation.", "simprocs", "maxSynthPendingDepth", "push_neg.",
   "backward.", "tactic.", "warningAsError"]

/-- The text of the first token of `stx`. -/
def headText (stx : Syntax) : Option String :=
  stx.getHead?.bind fun h => match h with
    | .atom _ v => some v
    | .ident _ _ n _ => some n.toString
    | _ => none

/-- The problems of one command's syntax tree. -/
partial def scan (stx : Syntax) (acc : Array String := #[]) : Array String := Id.run do
  let .node _ kind args := stx | return acc
  let mut acc := acc
  for a in args do
    if let .atom _ v := a then
      if forbiddenKeywords.contains v then acc := acc.push s!"`{v}` is not allowed"
      if v == "set_option" then
        let opt := args.findSome? fun x => if let .ident _ _ n _ := x then some n.toString else none
        if let some o := opt then
          unless allowedOptionPrefixes.any (o.startsWith ·) do
            acc := acc.push s!"the option `{o}` is not allowed"
  if let some h := headText stx then
    if h.startsWith "#" && h.length > 1 && (h.drop 1).all (fun c => c.isAlpha || c == '_') &&
        !allowedHashCommands.contains h then
      acc := acc.push s!"`{h}` is not allowed"
  if kind == ``Lean.Parser.Term.attrInstance then
    if let some a := args[1]? then
      if let some n := headText a then
        if forbiddenAttributes.contains n || n.startsWith "builtin_" then
          acc := acc.push s!"the attribute `{n}` is not allowed"
  for a in args do acc := scan a acc
  return acc

/-- Commands elaborated while linting: they change how later commands parse, and run no code of
the file. -/
def elaborated : List SyntaxNodeKind :=
  [``Lean.Parser.Command.open, ``Lean.Parser.Command.namespace, ``Lean.Parser.Command.section,
   ``Lean.Parser.Command.end]

/-- The imports of a file and the problems the filter finds, each with its line. -/
unsafe def lintFileUnsafe (path : System.FilePath) : IO (Array String × Array String) := do
  enableInitializersExecution
  let input ← IO.FS.readFile path
  let inputCtx := Parser.mkInputContext input path.toString
  let (header, parserState, messages) ← Parser.parseHeader inputCtx
  let imports := header.raw[2].getArgs.filterMap fun i =>
    i.getArgs.findSome? fun x => if let .ident _ _ n _ := x then some n.toString else none
  let (env, messages) ← Elab.processHeader header {} messages inputCtx
  if messages.hasErrors then
    let msgs ← messages.toList.mapM (·.toString)
    return (imports, #[s!"the header does not load: {"; ".intercalate msgs}"])
  let s : Frontend.State :=
    { commandState := Command.mkState env messages {}, parserState, cmdPos := parserState.pos }
  let go : FrontendM (Array String) := do
    let mut problems := #[]
    repeat
      updateCmdPos
      let cmdState ← getCommandState
      let scope := cmdState.scopes.head!
      let pmctx := { env := cmdState.env, options := scope.opts,
                     currNamespace := scope.currNamespace, openDecls := scope.openDecls }
      let before := cmdState.messages
      let (cmd, ps, msgs) := Parser.parseCommand inputCtx pmctx (← getParserState) before
      setParserState ps
      setMessages msgs
      let line := (inputCtx.fileMap.toPosition (cmd.getPos?.getD 0)).line
      if msgs.toList.length > before.toList.length && msgs.hasErrors then
        problems := problems.push s!"line {line}: does not parse"
      for p in scan cmd do problems := problems.push s!"line {line}: {p}"
      if elaborated.contains cmd.getKind then elabCommandAtFrontend cmd
      if Parser.isTerminalCommand cmd then break
    return problems
  let (problems, _) ← (go { inputCtx }).run s
  return (imports, problems)

@[implemented_by lintFileUnsafe]
opaque lintFile (path : System.FilePath) : IO (Array String × Array String)

end SigabaNeo.Platform.Lint
