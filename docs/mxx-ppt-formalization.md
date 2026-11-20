# mxx DSLからPPT性を形式証明するための実装調査・開発方針

**対象読者:** mxx、Lean、VCVioに初めて触れる実装者  
**調査基準日:** 2026年11月15日  
**目的:** mxx DSLの各プリミティブに、形式化されたチューリング機械上の計算実装と計算量証明を対応付け、DSLで構築した暗号アルゴリズム全体の**一様な多項式時間計算可能性（必要ならPPT）**をLeanで証明する。

> **要約:** チューリング機械・確率的PPT・基本的な計算の合成については、既存の **cslib-frontier** を利用できる。**PolyFun** は計算モデルを固定しない実装証拠・資源上界の抽象層、**VCVio** は暗号学的ゲームと確率・Oracleの意味論を提供する。mxxにも既にIRのLean Exportと、指定した仕事量を合成する `IRCost` が存在する。主な新規実装は、**mxxプリミティブの意味論を満たす具体的TMプログラムとその計算量証明**、**それらのIR全体への合成**、および**セキュリティパラメータに関する一様性の証明**である。VCVioの汎用Adequacy完成を待つ必要は必ずしもない。

## 1. 用語と、最終的に何を証明するか

- **数学的意味論（semantics）:** 演算が何を返すべきかの仕様。例：mxxの行列積が環 $R_Q$ 上の正しい行列積であること。
- **計算機バックエンド（machine backend）:** 実行の1ステップ、状態、メモリ、時間上界などがLean上で定義された**形式的な機械モデル**。ここでは主にcslib-frontierの確率的複数テープTMを指す。CUDA/GPU実行エンジンの意味ではない。
- **実装証拠（realizer / certificate）:** ある抽象関数を具体的な機械が正しく計算するという証明と、必要に応じて実行資源の上界。
- **符号化（encoding）:** Leanの整数・行列などを有限なビット列に変換する規約。計算時間は通常、**符号化した入力のビット長**に関して測る。
- **Adequacy／対応定理:** 抽象計算について得られた意味論・コストの主張が、選んだ機械の実際の実行にも当てはまることを保証する定理。
- **Strict uniform PPT:** セキュリティパラメータごとに異なる機械を自由に選ぶのではなく、**1つの固定された確率的TM**と**1つの多項式時間上界**を全パラメータ・入力に対して用いる。乱数の全経路に最悪時間の上界を課す。

目標となる命題は概念的には次のようになる。

$$
\exists M,\ p:\text{polynomial}.\quad
\forall \lambda,x,\quad
T_M(1^\lambda,\operatorname{enc}(x))\le p(\lambda+|\operatorname{enc}(x)|)
$$

加えて、$M$の出力がmxxの数学的意味論に一致することを証明する。確率的プログラムなら、出力**分布**の一致、または明示的な統計距離上界が必要になる。

**注意:** ある固定パラメータで有限の計算が実行できることだけでは、一様PPTは示せない。また、Leanで定義された任意の関数を自動的にPPTと判定することは一般にはできない。

## 2. 現在のライブラリの責務と実装状況

| 層 | 既存機能 | 未完了・注意事項 | mxxでの使い道 |
|---|---|---|---|
| **cslib-frontier** | `MultiTapePTM`、決定的多項式時間、`IsPPTOn`、`IsOraclePPTOn`、機械合成、`ppt`等の自動化 | あらゆるLean関数の自動PPT証明器ではない。個別のプリミティブや型について証明が必要 | **第一候補のTMバックエンド** |
| **PolyFun** | `StepClass`、`QuantitativeStepClass`、`Realizer`、`QuantitativeRealization`、`ExecutionTrace`、多項式資源上界、一部の合成証明 | コストは**選ばれたバックエンドに相対的**。cslib-frontierへの汎用的な対応・Oracle統合は未完成 | VCVioとの将来の一般化・共通インターフェース |
| **VCVio** | `OracleComp`、`ProbComp`、`evalDist`、安全性ゲーム、クエリコスト、バックエンド相対の `IsPPTBy` / `IsOraclePPTBy` | 無条件の標準的`IsPPT`、確率分布の橋渡し、汎用的なバックエンド対応は未完成 | **暗号安全性の証明**で利用 |
| **mxx** | Rust DSL→型付きIR、演算・loop・subgraph、Lean Export、`MxxRuntime`、`IRCost` | プリミティブの仕事量がTM実行時間を上界付ける証明がない。現行のExportは具体的に束縛されたパラメータ中心 | **対象言語と既存の意味論・コスト合成基盤** |

ここで「実装済み」は、当該リポジトリで確認できた機能を意味する。**全ライブラリを現在のバージョンのまま一つのLakeパッケージとしてビルドできる**という意味ではない。

### 2.1 cslib-frontier：すでに使える計算量証明

`IsPPTOn`は、形式化された確率的プログラムを**単一の有限状態・公平コインTM**が、入力の符号化長に関する多項式ステップ数で実現することを要求する。

実際のコードでは、概略次のように機械・多項式の存在を量化する。

```lean
-- cslib-frontier内の実際の定義から主要部を抜粋
-- (完全な型引数は原典参照)
def IsPPTOn (input : α ↪ List Bool) (output : β ↪ List Bool)
    (program : α → ProbComp β) : Prop :=
  ∃ (k : ℕ) (State : Type) (_ : Finite State)
    (machine : Turing.MultiTapePTM k Bool State) (c d : ℕ),
      ∀ a, (ProbComp.eval (program a)).map output =
        ProbComp.eval
          (machine.runClosed (c * ((input a).length + 1) ^ d) (input a))
```

`IsPPTOn.bind`は、証明済みの確率的プログラム2つを逐次合成してもPPTであることを保証する。より詳細な`ComputesInTimeOn.bind`では、先段の上界$t_1$と、後段の中間出力に関する上界$t_2'$から、**$2t_1+t_2'+4$**という具体的な合成時間上界を証明する（当該機械の合成方式に依存した式）。

`IsPPTOn`そのものは**多項式時間後に強制停止した出力分布**で定義される。一方、`ComputesInTimeOn`は時間上界までに実際に停止することも要求し、両者を結ぶ定理がある。既に機械を手で与えれば、個別の実行時間・停止性・分布の対応を証明できる。

参考：[`PPT.lean`](https://github.com/cslib-community/cslib-frontier/blob/main/CslibFrontier/Computability/Probabilistic/PPT.lean)、[`Time.lean`](https://github.com/cslib-community/cslib-frontier/blob/main/CslibFrontier/Computability/Probabilistic/Time.lean)、[`PPT/Composition.lean`](https://github.com/cslib-community/cslib-frontier/blob/main/CslibFrontier/Computability/Probabilistic/PPT/Composition.lean)、[`PPTTactic.lean`](https://github.com/cslib-community/cslib-frontier/blob/main/CslibFrontierTests/PPTTactic.lean)。

### 2.2 PolyFun：抽象計算と資源証明

`QuantitativeStepClass`は次のような情報を扱う。

- `Realizer`: 抽象関数を実装するバックエンドコードの証拠。
- `size`: 決められた符号化での値の大きさ。
- `cost`: バックエンドが定める実行コスト。
- `HasComposition` / `cost_compose_le`: 実行コードの合成と、**中間データの受け渡しコストを含む**計算量上界。

`QuantitativeRealization`は、Oracle計算の初期化（`init`）、次の問い合わせ・終了を観察する関数（`head`）、応答後の状態更新（`update?`）それぞれに実装証拠を結び付ける。`ExecutionTrace`は以下を数える。

1. バックエンド相対の通常計算量（`work`）
2. 問い合わせ数（`queries`）
3. 問い合わせ・応答の符号化バイト／ビット相当の通信量（`traffic`）
4. 最大内部状態サイズ（`peakStateSize`）
5. 最大readoutサイズ（`peakHeadSize`）

**重要な制限:** `cost`として好きな自然数を与えただけでは、TMで実際にそのステップ数以内に実行できることの証明にはならない。**具体的バックエンドによる実現性**を示す必要がある。

参考：[`Quantitative.lean`](https://github.com/Verified-zkEVM/PolyFun/blob/main/PolyFun/Realizability/Quantitative.lean)、[`Resource.lean`](https://github.com/Verified-zkEVM/PolyFun/blob/main/PolyFun/Realizability/Quantitative/Resource.lean)。

### 2.3 VCVio：暗号ゲームとPPTの接続

`ProbComp`は一様な乱数選択を持つ`OracleComp`の特殊例。`evalDist`はプログラムの出力分布を表す。`IsPPTBy Q` / `IsOraclePPTBy Q`は、**具体的なコストバックエンドQを明示した**PPT証明であり、汎用のTM-PPTと自動的に同一ではない。

公式[VCVio #906](https://github.com/Verified-zkEVM/VCVio/issues/906)は2026-11-15時点で未解決。未完了項目には、cslib-frontier連携、型付きOracleの符号化とAdequacy、`ProbComp`の確率意味論の一致などがある。

PolyFun側の[Issue #337](https://github.com/Verified-zkEVM/PolyFun/issues/337)は**Closed**だが、そこで言及される[試作PR #339](https://github.com/Verified-zkEVM/PolyFun/pull/339)は**Closed / unmerged**。一部のブリッジとテストは試作されビルドされたが、**現行mainに汎用Adequacyが統合済みであるとは扱わない**こと。

### 2.4 mxx：既存のLean連携とコスト合成

mxx DSLはRust上でグラフを構築し、IRがそれを保持する。`BuiltGraph.validate(bindings)`で具体的なパラメータを解決する。IRはLeanへの仕様Exportに対応する。

すでに存在する主なLeanコンポーネント：

- `MxxIR`: 実行関係、`parallel` / `iterate`等の構造、`IRCost.lean`。
- `MxxPrimitives`: 環、CRT、ガジェット分解、行列等の数学的補題。
- `MxxRuntime`: サンプラーテープ、分布、ハッシュの数学的仕様。
- Rust側 `mxx_ir_core::lean::cost::export`: コスト付きLean実行関係を生成。

`IRCost`では**指定された重み**の合計が形式的に正しく計算される。`CostedIterRuns`、`Costed.both`、`Costed.all`などがあり、loop反復回数を展開しなくても総仕事量を合成できる。ただし、`WorkSite { ..., units: u128 }`は**アプリケーションが与える不透明な重み**であり、TMのステップ数に対する健全性を持たない。`parallel`のコストは総仕事量であり、GPUの並列実行遅延ではない。

**もう一つ重要な点:** 現行mxxのLean Exportは固定パラメータの正しさを表現するものが中心であり、セキュリティパラメータ全体にわたる**一様なグラフ生成・実行**を別途形式化する必要がある。

参考：[`crates/dsl/SPEC.md`](https://github.com/MachinaIO/mxx/blob/main/crates/dsl/SPEC.md)、[`crates/ir-core/lean/README.md`](https://github.com/MachinaIO/mxx/blob/main/crates/ir-core/lean/README.md)、[`IRCost.lean`](https://github.com/MachinaIO/mxx/blob/main/crates/ir-core/lean/IRCost.lean)、[`src/cost.rs`](https://github.com/MachinaIO/mxx/blob/main/crates/ir-core/src/cost.rs)。

## 3. mxxで推奨する実装アーキテクチャ

```text
mxx Rust DSL
    ↓ build / freeze
mxx typed IR ──→ CPU / CUDA / HIP (既存の実行バックエンド)
    │
    ├──→ 既存Lean Export: 数学的な実行関係・確率仕様
    │
    └──→ 新規Complexity Export
              │
              ├── プリミティブごとのCertified TM implementation
              ├── IR構造に沿った合成（ループ・分岐・共有）
              └── 多項式時間・中間値サイズ・一様性の証明
                           ↓
              cslib-frontier: ComputableInPolyTime / IsPPTOn
                           ↓
              VCVio: 攻撃者・安全性ゲーム・識別優位
                           ↓
              Lean定理 → Prove2Meで共有
```

### 最初の方針：mxxからcslib-frontierへ直接接続

**最小構成ではVCVioやPolyFunの汎用Adequacy完成を待たない。** まずmxxプリミティブにcslib-frontierの具体的なTM実装・証明を与え、mxxの実行関係と一致することを示す。そのうえでcslib-frontierの合成定理を直接使う。

PolyFunを最初から必須依存にするよりも、**mxx-specificのLean証明層を独立させる**方が、小さな実験を開始しやすい。後から一般化可能な部分をPolyFunへ移植し、VCVioとの橋を追加する。

## 4. プリミティブの証明書（新規設計）

プリミティブごとに以下を用意する。例として行列加算を想定する。

```lean
-- これは提案するAPIの概念図。既存ライブラリのコンパイル可能な定義ではない。
structure PrimitiveTimeCertificate (op : MxxPrimitive) where
  implementation : TuringMachine
  encoding : InputOutputEncoding op
  correct : MachineComputes implementation (MxxSemantics op) encoding
  halts : AlwaysHalts implementation
  timeBound : ∀ input, Time implementation input ≤ primitiveBound op input
  outputBound : ∀ input, EncodedOutputSize implementation input ≤ outputSizeBound op input
```

実際のcslib-frontierでは`ComputableInPolyTime`、`ComputableTidilyInPolyTime`、`ComputesInTimeOn`等の**既存述語を使う**。上記の新しい構造をそのまま再実装する必要はない。`correct`と`timeBound`が既存述語の証拠から導けることを利用する。

必ず固定するもの：

- 入力・出力の**ビット列符号化**（整数は符号・大きさ、行列は次元と各係数、環は次数・法の表現）。
- 演算の**数学的仕様**との一致。
- TMの**停止性・最悪ステップ数**、出力サイズ。
- コスト上界が**値の実際のビット長**や$N$、行列次元、$\log Q$等に依存すること（$Q$を定数時間整数と扱わない）。

たとえば$R_Q=\mathbb Z_Q[X]/(X^N+1)$上の$a\times b$行列と$b\times c$行列の積は、学校式多項式乗算を使えば概念的に

$$
T_{\rm matmul}=O\!\left(abcN^2\,\mathrm{poly}(\log Q)\right)
$$

という**保守的な多項式上界**を目標にできる。NTT実装の形式検証はPPT性を示すだけなら必須ではない。ただし、厳密なビット演算上界と符号化・メモリコピーの証明は必要。

## 5. IRの合成に必要な規則と注意点

| mxx構造 | 証明すべき計算時間の形 | 重要な条件 |
|---|---|---|
| 各プリミティブ | $T_{op}(\text{size of input})$ | 実際のTMで実現・サイズを証明 |
| 逐次ノード | $T_A+T_B+\text{接続オーバーヘッド}$ | 中間値の符号化サイズを制限 |
| `parallel(k, body)` | $\sum_{i<k}T_{body}(i)$ | TMでは**総仕事量**。$k$の多項式上界 |
| `iterate(k, state, body)` | $\sum_{i<k}T_{body}(i,state_i)$ | 各状態サイズの多項式上界 |
| `select` | **全候補**の生成 + 選択 | mxxは選択候補を全部計算する |
| `Subgraph` | 本体の実行回数 × 本体コスト | 呼び出し単位で加算。共有ノードの二重計上を回避 |
| Graph build/validate | $T_{build}(\lambda)+T_{validate}(\lambda)$ | 一様なグラフ生成であること |

**重大な落とし穴:** すべてのプリミティブが多項式時間でも、途中でデータのビット長が反復ごとに倍増すれば、プログラム全体は指数時間になり得る。したがって、単に演算回数を数えるだけでは不十分。

`IRCost`の現行`u128`重みは、パラメータ付き・入力サイズ依存の多項式時間証明には不十分なので、**重みの見積もりと証明済みのTM時間上界を接続する別の証明レイヤー**を作る。最初から既存`IRCost`を破壊的変更する必要はない。

## 6. 「固定グラフ」と「一様PPT」の差を埋める

現在のmxxは`validate(bindings)`で具体パラメータの`ValidatedGraph`を作る。このグラフが有限であることは自明だが、それだけで暗号学的PPTにはならない。

目指すのは以下のいずれかの**単一の一様な実装**である。

1. **Uniform interpreter方式（推奨する初期案）:** 固定されたTMが、符号化されたmxx IRと実行入力を受け取り、IRを解釈する。IR構築器が$\lambda$から多項式時間でIRを生成でき、生成IRのサイズと実行資源が多項式であることを証明する。
2. **Uniform compiler方式:** $\lambda$からグラフを生成・コンパイルする処理まで、一つの固定TMで実装し、生成された実行プログラムのコストも含めて証明する。

どちらも、暗黙の巨大な計算済みテーブルやパラメータごとに任意に選んだ非一様コードを認めないことが必要。`encUnary λ`とビット長表現の違いにも注意する。

## 7. 確率的プリミティブとOracleの扱い

mxxには`uniform_residue`、`gaussian`、`sample_trapdoor`、`sample_preimage`、`hash_matrix`等がある。既存の`MxxRuntime.tapeMeasure`は**理想的なサンプリング分布**を定義しており、有限の公平コインTMによる効率的実装を自動的に与えるわけではない。

- **公平コイン・2冪サイズの一様分布:** 比較的直接的にTM実装を証明できる。
- **一般の有限一様分布:** 正確な棄却サンプリングは期待時間が有限でも、最悪時間が無界になり得る。Strict PPTのためには打ち切りと分布誤差の評価などが必要。
- **離散Gaussian:** 理想的な正確分布の実装と、厳密な最悪多項式時間での近似サンプリングを区別する。必要なら統計距離$\Delta\le\varepsilon(\lambda)$を証明。
- **Trapdoor / preimage sampling:** 数学的な値の範囲の保証と、サンプラーの分布・停止・計算量保証を分離する。
- **Random Oracle:** 理想Oracleを使うアルゴリズムのPPTは**Oracle相対PPT**。`hash_matrix`が具体的ハッシュ関数で実装できることと、理想Random Oracleと同一分布であることは異なる。

確率的プリミティブの誤差を持つ場合、合成全体の出力分布の誤差を明示的に蓄積して証明する必要がある。**決定的なプリミティブから先にEnd-to-Endを成立させる**。

## 8. 開発順序（最小構成→本来の目標）

| 段階 | 実装 | 完了条件 |
|---|---|---|
| **0. ツールチェーン整合** | Lean/Mathlib/CSLibのバージョンを揃える実験用ブランチ・Lakeパッケージ | mxx Leanの小さなfixtureとcslib-frontierを同じLean版でビルドできる |
| **1. 最小プリミティブ** | Boolean・固定幅値のコピー／加算、次に行列加算 | 数学的意味論と一致するTMと、ビット時間上界のLean証明 |
| **2. 合成** | 二つの演算、共有ノード、`select` | 合成した演算について一つのTM-PPT証明が出る |
| **3. ループ** | `parallel`、`iterate`、`Subgraph` | 中間値サイズ・反復回数を含む多項式上界 |
| **4. 主要演算** | 多項式行列積、CRT変換、分解 | mxx暗号処理の実例でPPT性を証明 |
| **5. 一様なファミリー** | パラメータ付きIR生成と固定TMの解釈 | 任意の許可された$\lambda$にわたる**uniform PPT** |
| **6. 確率** | 公平コイン、近似サンプリング、Oracle | 出力分布・統計距離・PPT性の証明 |
| **7. 暗号ゲーム** | VCVioと接続、Prove2Meに登録 | LWE識別器の成功確率とPPT性を一つの定理で扱う |

### 最初のEnd-to-Endテスト例

mxx DSLで「2つの行列を加算して、その結果に別の行列を加える」決定的グラフを構築する。Lean側で、(a) IR実行関係とTM実装の値が一致する、(b) 実行時間が各行列の要素数と係数ビット長の多項式である、(c) 合成後の機械が一つだけ存在する、という3点を証明する。

ここでは**最適化済みGPUカーネルと同じ命令列を検証する必要はない**。多項式時間の単純な参照実装があればよい。ただし「同じ数学的演算を計算する」ことの証明は必要。

## 9. モジュール配置・ビルド・信頼境界

推奨する追加構成例（**既存のパスではなく提案**）：

```text
mxx/
  crates/ir-core/lean/          # 既存 MxxIR / MxxRuntime / IRCost
  formal-complexity/           # 新しい独立Lakeパッケージ（実験中）
    Complexity/Encoding.lean
    Complexity/PrimitiveTM.lean
    Complexity/PrimitiveBounds.lean
    Complexity/Compose.lean
    Complexity/UniformFamily.lean
    Complexity/Probability.lean
    Tests/Smoke.lean
```

**現行ピン（2026-11-15確認）:** mxx Lean `v4.28.0`、VCVio/PolyFun `v4.35.0`、cslib-frontier `v4.36.0-rc2`。**異なるLean版の`.olean`をそのまま混ぜることはできない。** 独立Lakeパッケージを作るだけでは互換性は解決しないため、共通版への移植・ビルド検証が最初の作業になる。

証明の信頼境界を以下のように分ける。

1. **Lean kernel / 既存の形式化されたTM意味論**: 機械的証明の信頼基盤。
2. **mxx IR→Lean Exportの対応**: 現在のmxxではRustジェネレーターを信頼する部分が残る。完全なEnd-to-End保証には生成器の検証、または別実装による一致確認・証明を追加する。
3. **mxx IR→GPU backend**: 参照TMがPPTだという証明は、GPUカーネルの正しさ・実行時間を**保証しない**。
4. **乱数源**: 理想分布と実際の乱数生成器の一致・近似誤差は別の証明義務。

CIでは`lake build`、`#print axioms`、mxxのExport再生成差分検査に加え、**負のテスト**（指数的な中間値増大、型・符号化の食い違い、非一様なパラメータ別コード、未証明のサンプリングコストなどがPPT証明として受理されないこと）を入れる。

## 10. 今すぐ着手するための判断

**推奨方針:** まずmxxのLean実装にcslib-frontierの具体的なTM証明を接続する。PolyFun/VCVioの汎用Adequacyを独自forkで再構築するのは後回し。既存のcslib-frontier合成規則を使いつつ、mxx固有のIR→TM意味論・計算量の証明を行う。一般性のある新しい補題ができたらPolyFun/VCVio upstreamへのPRを検討する。

**最初に作るべき成果物は、(1) 1個の決定的mxxプリミティブのTM実装証明、(2) 2個のプリミティブの合成によるTM-PPT証明、(3) その証明が元のmxx IRの実行関係に一致することを示すLean定理、の3つ。** これで最もリスクの高い接続部分を小さく検証できる。

## 11. 一次資料（調査時点のコード・Issue）

1. [cslib-frontier: probabilistic PPT](https://github.com/cslib-community/cslib-frontier/blob/main/CslibFrontier/Computability/Probabilistic/PPT.lean)
2. [cslib-frontier: explicit-time probabilistic realization](https://github.com/cslib-community/cslib-frontier/blob/main/CslibFrontier/Computability/Probabilistic/Time.lean)
3. [cslib-frontier: PPT composition](https://github.com/cslib-community/cslib-frontier/blob/main/CslibFrontier/Computability/Probabilistic/PPT/Composition.lean)
4. [cslib-frontier: PPT tactic tests](https://github.com/cslib-community/cslib-frontier/blob/main/CslibFrontierTests/PPTTactic.lean)
5. [PolyFun: quantitative realizability](https://github.com/Verified-zkEVM/PolyFun/blob/main/PolyFun/Realizability/Quantitative.lean)
6. [PolyFun: polynomial resource certificates](https://github.com/Verified-zkEVM/PolyFun/blob/main/PolyFun/Realizability/Quantitative/Resource.lean)
7. [VCVio: computational complexity design](https://github.com/Verified-zkEVM/VCVio/blob/main/docs/design/computational-complexity.md)
8. [VCVio Issue #906](https://github.com/Verified-zkEVM/VCVio/issues/906)
9. [PolyFun Issue #337](https://github.com/Verified-zkEVM/PolyFun/issues/337)・[試作PR #339（未マージ）](https://github.com/Verified-zkEVM/PolyFun/pull/339)
10. [mxx DSL specification](https://github.com/MachinaIO/mxx/blob/main/crates/dsl/SPEC.md)
11. [mxx Lean package README](https://github.com/MachinaIO/mxx/blob/main/crates/ir-core/lean/README.md)
12. [mxx `IRCost.lean`](https://github.com/MachinaIO/mxx/blob/main/crates/ir-core/lean/IRCost.lean)・[mxx `WorkSite` implementation](https://github.com/MachinaIO/mxx/blob/main/crates/ir-core/src/cost.rs)
13. [mxx `RuntimeSampling.lean`](https://github.com/MachinaIO/mxx/blob/main/crates/ir-core/lean/RuntimeSampling.lean)
14. [VCVio: backend-relative PPT](https://github.com/Verified-zkEVM/VCVio/blob/main/VCVio/CryptoFoundations/Asymptotics/ComputationalComplexity.lean)

---

*この文書はGitHubで確認できる実装・ドキュメントと、そこから導いた推奨設計を区別して記載した技術的な計画書である。設計例として示した`PrimitiveTimeCertificate`等は既存APIではない。*
