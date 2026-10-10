import time, sys, numpy as np
from multiprocessing import Pool
import ringbb_rig as A
import ringbb_rig_fast as B

def job(args):
    which, n, k, rho, P, boxes = args
    mod = A if which == "orig" else B
    dl, dh, rih, rm = P
    mod.run_bb_rig(n, k, rho, dl, dh, rih, rm, 0.02, 10, boxes[0])
    t = time.time(); tot = 0
    for b in boxes:
        tot += mod.run_bb_rig(n, k, rho, dl, dh, rih, rm, 0.02, int(1e12), b)[0]
    return which, tot, time.time() - t

if __name__ == "__main__":
    n, k, rho = 15, 7, 3.52135696470617
    P = A.rigorous_params(n, rho)
    boxes = A.presplit(n, k, rho, P, 400)[:60]
    with Pool(2) as pool:
        for r in pool.map(job, [("orig", n, k, rho, P, boxes), ("fast", n, k, rho, P, boxes)]):
            print(r)
