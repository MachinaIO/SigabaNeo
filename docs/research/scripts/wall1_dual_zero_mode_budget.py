"""Zero completion-dual contribution and conditional remaining-frequency budgets."""
from mpmath import iv

def main():
    iv.dps=70;I=iv.mpf;q=3329;n=118;d=10;k=6
    V506=iv.pi**253/iv.factorial(253)
    R2=I('1.21')*iv.exp(2*(I(386)*iv.log(q)-iv.log(V506))/506)-2
    gamma=I(n)/(2*R2)
    logF=I(d*k)*iv.log(q)+k*gamma*R2+I(n*k)*(iv.log(iv.pi)/2-iv.log(q)-iv.log(gamma)/2)
    M=min(I(q**d),(iv.pi**5/iv.factorial(5))*(iv.sqrt(R2)+iv.sqrt(d)/2)**d,key=lambda x:x.b)
    lF=logF/iv.log(10);lM=k*iv.log10(M)
    targetlog=I('39.9478');desired=I('-12')
    baseline_target=targetlog+lF-lM
    budget_current=lM-lF
    budget_target=desired-baseline_target
    assert budget_current>0 and budget_target>0
    print('radius',iv.sqrt(R2),'gamma minimizer',gamma)
    for label,value in [('log10 F0 lower contribution',lF),('log10 current M10^6',lM),('log10 allowed TOTAL/zero to beat current',budget_current),('conditional leading term log10 at zero contribution',baseline_target),('log10 allowed TOTAL/zero for target1e-12',budget_target),('log10 allowed row geometric multiplier current',budget_current/n),('log10 allowed row geometric multiplier target',budget_target/n)]:print(label,value)
    print('budgets are upper obligations on total/zero; zero is not an upper bound.')
if __name__=='__main__':main()
