"""Check affine chart indexing and signed residues by direct modular arithmetic."""

from collections import Counter
from math import gcd, isqrt, lcm
import unittest

from experiments.offset_gap_lift import affine_classes, choose_divisor


def reference(n, trace, s, v, d, square8):
    """Independent CRT construction with the full fourth-power projector."""
    K = (s*v)**2
    e = v**4*pow(v**4,-1,s**4)
    sign = 1-2*e
    if square8 and (s*v)%2 == 0:
        u = pow(trace,-1,8*d*d)
        z = sign*(trace-2*n*K*u)+2*(e*s**4-(1-e)*v**4)*u
        return z % (16*K*d*d), 16*K*d*d
    u = pow(trace,-1,d*d)
    modulus = 2*K*d*d
    z = sign*(trace-2*n*K*u) % modulus
    small = v*v*pow(v*v,-1,s*s)
    legacy = s*s-v*v + (1-2*small)*(trace-s*s-v*v)
    if (z-legacy)%(4*K):
        z += modulus
    assert (z-legacy)%(4*K)==0
    return z,lcm(modulus,4*K)


class GapLiftTests(unittest.TestCase):
    def test_progressions_equal_independent_per_position_crt(self):
        for s,v in ((1,1),(2,1),(4,3),(5,3),(7,6),(9,8),(11,9)):
            for d in range(1,17):
                if s*v % d:
                    continue
                n,t = 117449,342
                first = 1+(s+v-1)%2
                for extra in (False,True):
                    work = Counter()
                    rows = affine_classes(n,t,s,v,first,31,d,square8=extra,work=work)
                    baseline = affine_classes(n,t,s,v,first,31,d,square8=extra,split_only=True)
                    self.assertEqual([r[:3] for r in rows],[r[:3] for r in baseline])
                    seen = set()
                    for (st,stride,count,r,m,mod),base in zip(rows,baseline):
                        for x in range(count):
                            i=st+stride*x
                            self.assertNotIn(i,seen)
                            seen.add(i)
                            trace=2*t*s*v + first+2*i
                            self.assertEqual(((r+m*x)%mod,mod),reference(n,trace,s,v,d,extra))
                            self.assertEqual((r+m*x)%base[5],(base[3]+x*base[4])%base[5])
                    self.assertEqual(seen,{i for i in range(31) if gcd(first+2*i,d)==1})
                    self.assertEqual(work['nonunit_offsets'],31-len(seen))
                    self.assertEqual(work['unit_classes'],len(rows))

    def test_oriented_difference_inherits_lift_at_true_traces(self):
        for p,q in ((17,23),(31,61),(257,457)):
            n=p*q
            t=isqrt(n)
            for v in range(1,8):
                for s in range(v,13):
                    k=s*v
                    j=p*s*s+q*v*v-2*t*k
                    if gcd(s,v)!=1 or gcd(j,k)!=1:
                        continue
                    d=choose_divisor(k,12)
                    start=j-8
                    for options,divisor in (({},d),({'square8':True},d),({'square24':True},1),
                                            ({'trace_units':True},1)):
                        rows=affine_classes(n,t,s,v,start,9,divisor,**options)
                        sign=p*s*s-q*v*v
                        matches=[sign % m == (r+step*((4-i)//stride)) % m
                                 for i,stride,count,r,step,m in rows
                                 if 4>=i and (4-i)%stride==0 and (4-i)//stride<count]
                        self.assertEqual(matches,[True])

    def test_self_inverse_24_keeps_the_nonunit_trace_fallback(self):
        for n in (5*7,7*13,3*17):
            t=isqrt(n)
            for s,v in ((4,3),(5,2),(3,1)):
                k=s*v
                first = 1+(s+v-1)%2
                setup=Counter()
                rows=affine_classes(n,t,s,v,first,28,1,square24=True,work=setup)
                split=affine_classes(n,t,s,v,first,28,1,square24=True,split_only=True)
                self.assertEqual([a[:3] for a in rows],[a[:3] for a in split])
                self.assertEqual(setup['class_inverses'],0)
                parity_only = k%2!=0
                expected = {i for i in range(28) if parity_only or n%3==0 or gcd(first+2*i,gcd(k,3))==1}
                seen = set()
                for i,stride,count,r,step,mod in rows:
                    for m in range(count):
                        pos=i+stride*m
                        trace=first+2*pos+2*t*k
                        seen.add(pos)
                        if parity_only:
                            rem,period = reference(n,trace,s,v,1,False)
                        elif n%3 and trace%3:
                            e=v**4*pow(v**4,-1,s**4)
                            u=pow(trace,-1,24)
                            rem=(1-2*e)*(trace-2*n*k*k*u)+2*(e*s**4-(1-e)*v**4)*u
                            period=48*k*k
                        else:
                            rem,period=reference(n,trace,s,v,1,True)
                        self.assertEqual(mod,period)
                        self.assertEqual((r+step*m)%mod,rem%period)
                self.assertEqual(seen,expected)

    def test_budget_and_validation(self):
        work={}
        self.assertEqual(choose_divisor(42,8,work),7)
        self.assertEqual(work['divisor_trials'],2)
        self.assertEqual(affine_classes(117449,342,4,3,1,0,12),[])
        for args in [(1,3,1,7,2),(2,2,2,7,2),(2,3,0,7,2)]:
            with self.assertRaises(ValueError):
                affine_classes(117449,342,*args)

    def test_trace_unit_fibers_against_exact_weighted_factor_crt(self):
        for n in (35,77,91,391):
            for s,v in ((1,1),(2,1),(3,1),(4,3),(5,3),(9,7)):
                t=isqrt(n)
                K=(s*v)**2
                first=1+(s+v-1)%2
                work=Counter()
                rows=affine_classes(n,t,s,v,first,51,1,trace_units=True,work=work)
                split=affine_classes(n,t,s,v,first,51,1,trace_units=True,split_only=True)
                self.assertEqual([r[:3] for r in rows],[r[:3] for r in split])
                returned={}
                for start,stride,count,r,b,m in rows:
                    for step in range(count):
                        pos=start+stride*step
                        self.assertNotIn(pos,returned)
                        returned[pos]=((r+b*step)%m,m)
                for pos in range(51):
                    S=first+2*pos+2*t*s*v
                    signed=[]
                    for p in range(24):
                        if gcd(p,24)!=1:
                            continue
                        q=n*pow(p,-1,24)%24
                        if (S-p*s*s-q*v*v)%24:
                            continue
                        # Solve independently for z using both exact factor-unit congruences.
                        left=2*s*s*p-S
                        right=S-2*v*v*q
                        digit=((right-left)//48)*pow(s*s,-1,v*v)%(v*v)
                        signed.append((left+48*s*s*digit)%(48*K))
                    if not signed:
                        self.assertNotIn(pos,returned)
                    else:
                        period=gcd(48*K,*(z-signed[0] for z in signed))
                        self.assertEqual(returned[pos],(signed[0]%period,period))
                self.assertEqual(work['class_inverses'],0)
                self.assertEqual(work['trace_rejected_offsets'],51-len(returned))
        self.assertEqual(affine_classes(51,7,3,2,1,20,1,trace_units=True),
                         affine_classes(51,7,3,2,1,20,1))

    def test_compressed_trace_chart_equals_all_eight_explicit_unit_images(self):
        def expand(rows):
            result = {}
            for start,stride,count,r,step,mod in rows:
                for i in range(count):
                    pos = start+stride*i
                    self.assertNotIn(pos,result)
                    result[pos] = (mod,(r+step*i)%mod)
            return result

        quotients = set()
        for n in (25,29,31,35,37,41,43,47):
            for s in range(1,25):
                for v in range(1,s+1):
                    if gcd(s,v)!=1:
                        continue
                    quotients.add(24//gcd(s*s+n*v*v,24))
                    first = (s+v)%2+2*((n+s-v)%12)
                    for length in (1,7,29):
                        opts = (n,isqrt(n),s,v,first,length,1)
                        compressed = affine_classes(*opts,trace_units=True)
                        explicit = affine_classes(*opts,trace_units=True,explicit_trace=True)
                        self.assertLessEqual(len(compressed),2)
                        self.assertEqual(expand(compressed),expand(explicit))
        self.assertEqual(quotients,{1,2,3,4,6,8,12,24})


if __name__=='__main__':
    unittest.main()
