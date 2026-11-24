"""Radius sensitivity of the existing degree-12 reference term only.

Reuse the production count function without executing the unrelated, costly
module-level incidence checks. No full certificate at changed radii is claimed.
"""
import ast
from pathlib import Path
from mpmath import iv


def main():
    iv.dps = 80
    I = iv.mpf
    volume = [I(1), I(2)]
    for n in range(2,519):
        volume.append(2*iv.pi*volume[n-2]/n)
    source = Path(__file__).with_name('wall1_affine_void_moments.py')
    tree = ast.parse(source.read_text())
    node = next(n for n in tree.body
                if isinstance(n,ast.FunctionDef) and n.name == 'candidate_lower')
    namespace = {'iv':iv, 'I':I, 'volume':volume}
    exec(compile(ast.Module(body=[node],type_ignores=[]),str(source),'exec'),namespace)
    radius = iv.sqrt(I('1.21')*iv.exp(
        2*(386*iv.log(3329)-iv.log(volume[506]))/506)-2)
    results = {}
    for factor in ('1','.9999','.99977','.99976','.9995','.999','.99'):
        mu = namespace['candidate_lower'](518,radius*I(factor))/3329**400
        term = total = I(1)
        for k in range(1,13):
            term = term*mu/k
            total += term
        baseline = 1/(I('.280')*total)
        results[factor] = baseline
        print(factor, 'count lower / q^400:',iv.nstr(mu,16),
              'degree-12 reference:',iv.nstr(baseline,16))
    assert results['1'].b < I('9.131e-13').a
    assert results['.99977'].b < I('3.922e-12').a
    assert results['.99976'].a > I('3.922e-12').b
    assert results['.9995'].a > I('1.8969e-11').b
    print('Certified: a 0.024% shrink already exceeds the budget in this reference term.')
    print('No changed-radius full cumulant bound or actual failure lower bound is claimed.')


if __name__ == '__main__':
    main()
