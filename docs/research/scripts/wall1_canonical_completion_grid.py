"""Bounded h24/r11/H6 canonical completion-grid diagnostic, not a full run."""
import time
from mpmath import iv
import wall1_anchored_dual_completion as completion


def main():
    iv.dps=60
    I=iv.mpf;q=3329
    radius_sq=I('1.21')*iv.exp(
        2*(386*iv.log(q)-iv.log(iv.pi**253/iv.factorial(253)))/506)-2
    state={'iv':iv,'q':q,'N':518,'radius':iv.sqrt(radius_sq)}
    original_orders=completion.FULL_HOLDER_ORDERS
    original_grid=completion.GAMMA_GRID
    dense_orders=tuple(range(2,48))
    dense_grid=tuple(dict.fromkeys(
        original_grid+tuple(f'{j}e-9' for j in range(150,1001,25))))
    settings=(('baseline',original_orders,original_grid),
              ('only_L13',tuple(sorted(set(original_orders+(13,)))),original_grid),
              ('orders',dense_orders,original_grid),
              ('gamma',original_orders,dense_grid),
              ('both',dense_orders,dense_grid))
    baselines={}
    started=time.monotonic()
    try:
        for label,orders,grid in settings:
            completion.FULL_HOLDER_ORDERS=orders
            completion.GAMMA_GRID=grid
            for determinant in (12,16):
                for mode in ('same','free'):
                    beta=None if mode=='same' else I(518)/(2*radius_sq)
                    cap,gamma=completion.completion_details(
                        state,11,24,anchor_size=6,free_beta=beta,
                        coordinate_count=518,anchor_gram_det=determinant)
                    key=(determinant,mode)
                    if label=='baseline':baselines[key]=cap
                    assert cap.a>0 and cap.b<=baselines[key].b
                    print(label,'D',determinant,'mode',mode,'gamma',gamma,
                          'logcap',iv.log10(cap),
                          'gain_decades',iv.log10(baselines[key]/cap),flush=True)
        print('Elapsed seconds:',time.monotonic()-started,flush=True)
    finally:
        completion.FULL_HOLDER_ORDERS=original_orders
        completion.GAMMA_GRID=original_grid


if __name__=='__main__':
    main()
