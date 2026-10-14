"""Check selected exact identities and polynomial coefficient signs in the article.

Requires SymPy 1.14.0.
"""
import json
import sympy as s

c, t, K, j, H, z, w, u, v, delta, r, M = s.symbols('c t K j H z w u v delta r M')
passed = []


def identity(name, left, right):
    residual = s.factor(left - right)
    if residual != 0:
        raise AssertionError((name, residual))
    passed.append(name)


def positive_coefficients(name, expr, variables):
    polynomial = s.Poly(s.expand(expr), *variables)
    if not all(coefficient > 0 for coefficient in polynomial.coeffs()):
        raise AssertionError((name, polynomial))
    passed.append(name)


def main():
    half = (c + t) / 2
    B = K ** 2 + (2 * c - t - 1) * K + c ** 2
    T = 2 * K + c
    lp = K - t - j
    rho = c * (1 + w) - 1
    seed_t = c * (w ** 2 + 2 * w) - 2
    N = T * (K + rho - t) ** 2 - (T - t) * B
    expanded_seed = N.subs({t: seed_t, K: c + seed_t + 1 + z})
    identity('4.7–4.8 seed expansion', expanded_seed,
             c ** 3 * (2*w + 2*w**2 - w**4) + c**2*(w-1)**2
             + (c**2*(4*w+w**2-w**4)+c*(w-1)**2)*z + c*w*(2-w)*z**2)
    endpoint = (half + j) / K + lp**2 / (K * lp + c**2) + t/T - 1
    identity('4.11 capped endpoint', endpoint,
             c/(2*K)*((T-t)/T-2*c*lp/(K*lp+c**2)))
    baseline = (half+j)/(K-delta) + (K-t-j)/(K+c) + t/T - 1
    P = (-2*c*K**2 + K*(c**2+4*c*delta+4*c*j+3*c*t+4*delta*j+2*delta*t)
         + c**3+2*c**2*delta+2*c**2*j+c**2*t+2*c*delta*j)
    identity('6.3 cleared density polynomial', 2*(K+c)*(K-delta)*T*baseline, P)
    identity('6.4 positive root test', P.subs(K,c+t+j+2*delta),
             (c+2*delta)*(3*c*j+c*t+4*delta*j+2*delta*t+2*j**2+3*j*t+t**2))
    identity('8.2 chord square', 18*c*(H+1)-4*(c+H+1)**2,
             2*(2*c-H-1)*(2*H+2-c))
    R = s.Symbol('R')
    n = (T*(K+R-1-t)**2-(T-t)*B).subs({t:2*H-c,K:2*H+1+z})
    affine = s.rem(n, R**2-2*c*(H+1), R)
    identity('8.3 affine coefficient', s.diff(affine,R),
             4*z**2+(8*H+6*c+4)*z+c*(8*H+2*c+4))
    Q = ((t+2)*z**2+2*((H-1)*t+5*H+1)*z+c*(t**2+6*H+2))
    identity('8.3 chord substitution', affine.subs(R,2*(c+H+1)/3), Q.subs(t,2*H-c)/3)
    C = 8*H**2+4*H*t**2-4*H*t-2*t**3-t**2-2*t-1
    identity('8.4 margin identity', (2*Q-(2*H+1+z+c)**2).subs(c,2*H-t),
             (2*t+3)*z**2+((4*H-2)*t+12*H+2)*z+C)
    Cuv = C.subs({H:u+(2*(v+1)+1)/3,t:v+1})
    identity('8.5 positive substitution', Cuv,
             8*u**2+4*u*v**2+s.Rational(44,3)*u*v+16*u+s.Rational(2,3)*v**3
             +s.Rational(29,9)*v**2+s.Rational(14,3)*v+2)
    positive_coefficients('8.5 coefficients', Cuv, (u,v))
    capped = (4*K**2+(6-13*c)*K-12*c**2).subs(K,4*c-1+w)
    identity('8.2 capped numerator substitution', capped,4*w**2+(19*c-2)*w+5*c-2)
    positive_coefficients('8.2 capped sign for c >= 1', capped.subs(c,1+u),(u,w))
    density_r = baseline.subs({delta:r/2,c:2*H-t,K:2*H+j+r})
    kr, mr, cr, tr = 2*H+j+r, 3*H+j+r, 2*H-t, 2*(2*H+j+r)+2*H-t
    identity('8.12 quantitative separation', density_r,
             (cr+r)*(j*mr+t*(H+r/2))/((kr+cr)*(kr-r/2)*tr))
    k, cap = M-H, 2*H-t
    alpha = lambda m: 1+1/(m*(m-1))
    F = (H+1)/(k-1)+(k-t-1)/(k+cap)+t/(2*M-t-1)
    F0 = (H+1)/(M-H-1)+(M-H-1)/(M+H)
    identity('9.5 structural difference', F-F0,
             t*(k-1)*(k-t-1)/((M+H)*(M+H-t)*(2*M-t-1)))
    identity('9.6 structural threshold', F0-alpha(M),
             H*((3*H+4-M)*M*(M-1)+H+1)/(M*(M-1)*(M-H-1)*(M+H)))
    G = lambda a,b: (H+a)/(k-b)+(k-t-a)/(k+cap)+t/(2*M-t-1)
    identity('9.10 bound comparison', G(1,2)-G(2,1),
             ((H-cap)*k+cap*(H+3)+2)/((k-2)*(k-1)*(k+cap)))
    identity('9.11 H=1 bound', (G(2,1)-alpha(M)).subs({H:1,t:1}),
             (-M**2+14*M-12)/(2*M*(M-1)*(M-2)))
    g = G(2,1).subs(H,2)
    identity('9.12 H=2 monotonicity', g-g.subs(t,1),
             (t-1)*((2*M-1)/((2*M-t-1)*(2*M-2))-6/((M+2-t)*(M+1))))
    identity('9.13 M=11 endpoint', (g-alpha(M)).subs({t:1,M:11}),s.Rational(9,220))
    identity('9.13 M=12 endpoint', (g-alpha(M)).subs({t:1,M:12}),s.Rational(107,5148))
    identity('9.15 short-width bound', (G(j,delta)-1).subs(t,0),
             (3*H**2-H*M+2*H*j+2*H*delta+j*delta)/((M-H-delta)*(M+H)))
    mix = 2/(M-3)+1/(M-2)+(M-3)/(M+1)
    identity('9.16 mixed-width charge', mix-1,
             (11-M)/((M-2)*(M+1))+2/((M-3)*(M-2)))
    identity('9.16 M=12 endpoint', (mix-alpha(M)).subs(M,12),s.Rational(179,25740))
    bounds = [2/(K-1)+(K-4)/K+3/(K+2), 2/(K-2)+(K-6)/K+5/(K+2),
              3/(K-1)+(K-6)/K+1/(K+1)+3/(K+2), 3/(K-1)+(K-6)/K+5/(K+4)]
    differences = [(K**2*(K-3)+4*K+10)/(K*(K-1)*(K+1)*(K+2)),
                   (K**2*(K-6)+18*K+28)/(K*(K-2)*(K+1)*(K+2)),
                   (K**2*(K-3)+6*K+14)/(K*(K-1)*(K+1)*(K+2)),
                   2*(K**2*(K-4)*(K+1)+27*K+24)/(K*(K-1)*(K+1)*(K+2)*(K+4))]
    for i,(bound,difference) in enumerate(zip(bounds,differences)):
        name = 'ABCD'[i]
        identity('9.19 pattern '+name, bound-alpha(K+(2 if i==3 else 1)),difference)
        numerator = s.fraction(difference)[0]
        positive_coefficients('9.19 sign '+name,numerator.subs(K,(9 if i==3 else 7)+z),(z,))
    print(json.dumps({'status':'PASS','sympy':s.__version__,'checks':len(passed),
                      'verified_identities_and_signs':passed},indent=2))


if __name__ == '__main__':
    main()
