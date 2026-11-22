#!/usr/bin/env python3
"""Exact algebra checks for the existence argument of MODULAR_EXISTENCE.md.

Run with Python 3 and SymPy installed, from the repository root:
    uv run --with sympy python -I scripts/check_modular_identities.py

This checks finite polynomial/rational identities and cusp coefficients. It does
not prove the analytic theta transformation laws, convergence, boundary-to-kernel
correspondence, or any Lean theorem. See
SphereCetiRoadmap/CoefficientMagic/MODULAR_EXISTENCE.md.  This is a development check
and is not part of CI.

Conventions: q = exp(2*pi*i*tau), t = q**(1/2), delta = 2*pi*i.
The scalar inputs B=delta*B0 and C=delta**2*C0 are rescaled so that
the cusp matrices have rational entries. D_tau=delta*(t/2)*d/dt.
"""

import sympy as sp


def check_covariants():
    a, b = sp.symbols("a b")
    rho_s = sp.Matrix([[-1, 3], [1, 1]]) / 2
    rho_t = sp.diag(1, -1)
    vec = sp.Matrix([a, b])
    quad = sp.Matrix([-a*a + 3*b*b, 2*a*b])
    for rho in (rho_s, rho_t):
        transformed = rho * vec
        substituted = quad.subs(
            {a: transformed[0], b: transformed[1]}, simultaneous=True
        )
        assert all(sp.expand(e) == 0 for e in substituted - rho*quad)
    assert sp.factor(sp.Matrix.hstack(vec, quad).det()) == 3*b*(a-b)*(a+b)
    x, y = sp.symbols("x y")
    determinant = (3*b*(a*a-b*b)).subs({a: x+y/2, b: -y/2})
    theta_delta = (x*y*(x+y))**2/256
    assert sp.expand(determinant**2-576*theta_delta) == 0
    assert rho_s**2 == sp.eye(2)
    assert rho_t**2 == sp.eye(2)
    assert (rho_s*rho_t)**3 == sp.eye(2)


def check_six_by_six_relations():
    tau = sp.symbols("tau", nonzero=True)

    def frame(z):
        return sp.Matrix([
            [1, z, z*z, 1, 0, 0],
            [0, 1, 2*z, 0, 0, 0],
            [0, 1/z, 1, 2, 0, 0],
            [0, 0, 1, 2, 0, 0],
            [0, 0, -1-2*z, 0, -1, 0],
            [0, 0, z*z, 1, 0, -1],
        ])

    swap = sp.zeros(6)
    for i in range(3):
        swap[i, i+3] = 1
        swap[i+3, i] = 1
    translation = sp.diag(1, 1, 1, -1, 1, 1)

    def inversion(z):
        return sp.simplify(frame(-1/z).inv() * swap * frame(z))

    assert sp.factor(frame(tau).det()) == -4
    assert sp.simplify(inversion(-1/tau)*inversion(tau)) == sp.eye(6)
    rotate = lambda z: -1/(z+1)
    st_cube = (
        inversion(rotate(rotate(tau))+1)*translation
        * inversion(rotate(tau)+1)*translation
        * inversion(tau+1)*translation
    )
    assert sp.simplify(st_cube) == sp.eye(6)

    half = sp.Rational(1, 2)
    splitting = sp.Matrix([
        [half, 0, 0, 0, 0, half],
        [0, half, half, 0, half, 0],
        [0, 0, 1, 0, 0, 0],
        [half, 0, 0, 0, 0, -half],
        [0, half, -half, 0, -half, 0],
        [0, 0, 0, 1, 0, 0],
    ])
    plus = sp.Matrix([[tau**-2, 0, 0], [2/tau, 1, 0], [1, tau, tau*tau]])
    minus = sp.Matrix([[-half, 1/tau-tau/2, 3*half],
                       [0, 1, 0], [half, tau/2, half]])
    assert sp.simplify(splitting*inversion(tau)*splitting.inv()) == sp.diag(plus, minus)
    assert splitting*translation*splitting.inv() == sp.diag(1, 1, 1, 1, 1, -1)


def check_derivative_blocks():
    tau = sp.symbols("tau", nonzero=True)
    f, df, ddf, b, db, c = sp.symbols("F DF DDF B DB C")
    for k in (-4, -12):
        p = sp.Matrix([f, sp.Rational(2, k)*df+b,
                       sp.Rational(1, k*(k+1))*ddf+sp.Rational(1, k+2)*db+c])
        substitutions = {
            f: tau**k*f,
            df: tau**(k+2)*df+k*tau**(k+1)*f,
            ddf: (tau**(k+4)*ddf+(2*k+2)*tau**(k+3)*df
                  +k*(k+1)*tau**(k+2)*f),
            b: tau**(k+2)*b,
            db: tau**(k+4)*db+(k+2)*tau**(k+3)*b,
            c: tau**(k+4)*c,
        }
        transformed = p.subs(substitutions, simultaneous=True)
        expected = sp.Matrix([
            tau**k*p[0],
            tau**(k+2)*p[1]+2*tau**(k+1)*p[0],
            tau**(k+4)*p[2]+tau**(k+3)*p[1]+tau**(k+2)*p[0],
        ])
        assert all(sp.expand(e) == 0 for e in transformed-expected)


def cusp_data():
    t = sp.symbols("t")
    order = 8

    def truncate(expr):
        return sp.series(expr, t, 0, order).removeO().expand()

    # Standard defining Fourier series, evaluated to more terms than the
    # finite coefficient checks require.
    e4 = 1 + 240*sum(sp.divisor_sigma(n, 3)*t**(2*n) for n in range(1, 4))
    e6 = 1 - 504*sum(sp.divisor_sigma(n, 5)*t**(2*n) for n in range(1, 4))
    delta_over_q = sp.Integer(1)
    for n in range(1, 4):
        delta_over_q = truncate(delta_over_q * (1-t**(2*n))**24)

    # theta_4 = 1 + 2 sum_{n>=1} (-1)^n t^(n^2).
    theta4 = 1 + 2*sum((-1)**n*t**(n*n) for n in range(1, 3))
    theta4_four = truncate(theta4**4)
    # theta_2 = 2*t^(1/4) sum_{n>=0} t^(n(n+1)).
    theta2_four = truncate(16*t * (sum(t**(n*(n+1)) for n in range(3)))**4)
    a = truncate(theta4_four + theta2_four/2)
    b = truncate(-theta2_four/2)
    v2 = sp.Matrix([a, b])
    w4 = sp.Matrix([truncate(-a*a+3*b*b), truncate(2*a*b)])

    assert truncate(e4**3-e6**2-1728*t**2*delta_over_q) == 0
    assert a.coeff(t, 0) == 1
    assert b.coeff(t, 1) == -8

    def denominator(power):
        return t**(-2*power)*truncate(delta_over_q**(-power))

    return t, e4, e6, v2, w4, denominator


def check_dimension(dimension):
    t, e4, e6, v2, w4, denominator = cusp_data()
    q_derivative = lambda f: sp.expand(t*sp.diff(f, t)/2)
    coefficient = lambda f, exponent: sp.expand(f).coeff(t, exponent)

    if dimension == 8:
        u, v, w, x, r, s = variables = sp.symbols("u v w x r s")
        k = -4
        inv_delta = denominator(1)
        f = sp.expand(u*e4**2*inv_delta)
        b0 = sp.expand(v*e4*e6*inv_delta)
        c0 = sp.expand((w*e4**3+x*e6**2)*inv_delta)
        minus = (r*e4**2*v2+s*e6*w4)*inv_delta
        witness = sp.Matrix([-3, sp.Rational(3, 2), -sp.Rational(41, 144),
                             -sp.Rational(31, 144), -2, 1])
        expected = sp.Matrix([
            [sp.Rational(1, 2), 1, 0, 0, 0, 0],
            [sp.Rational(1, 12), sp.Rational(1, 2), 1, 1, 0, 0],
            [0, 0, 744, -984, 0, 0],
            [0, 0, 0, 0, -8, -16],
            [1, 0, 0, 0, -1, 1],
        ])
        expected_lambda_over_pi = 180
    else:
        assert dimension == 24
        u, v, w, x, y, r, s, z = variables = sp.symbols("u v w x y r s z")
        k = -12
        inv_delta = denominator(2)
        f = sp.expand((u*e4**3+v*e6**2)*inv_delta)
        b0 = sp.expand(w*e4**2*e6*inv_delta)
        c0 = sp.expand((x*e4**4+y*e4*e6**2)*inv_delta)
        minus = (r*e4**3*v2+s*e6**2*v2+z*e4*e6*w4)*inv_delta
        witness = sp.Matrix([-sp.Rational(49, 8), sp.Rational(25, 8), 1,
                             -sp.Rational(23, 1760), -sp.Rational(169, 1760),
                             -sp.Rational(8, 9), -sp.Rational(10, 9), 1])
        expected = sp.Matrix([
            [sp.Rational(1, 3), sp.Rational(1, 3), 1, 0, 0, 0, 0, 0],
            [sp.Rational(1, 33), sp.Rational(1, 33), sp.Rational(1, 5),
             1, 1, 0, 0, 0],
            [sp.Rational(64, 11), -sp.Rational(80, 11), sp.Rational(12, 5),
             1008, -720, 0, 0, 0],
            [0, 0, 0, 401544, -54648, 0, 0, 0],
            [0, 0, 0, 0, 0, -8, -8, -16],
            [0, 0, 0, 0, 0, -6176, 7648, 3008],
            [1, 1, 0, 0, 0, -1, -1, 1],
        ])
        expected_lambda_over_pi = 98280

    p1_scaled = sp.Rational(2, k)*q_derivative(f) + b0
    p2_scaled = (sp.Rational(1, k*(k+1))*q_derivative(q_derivative(f))
                 + sp.Rational(1, k+2)*q_derivative(b0) + c0)
    m0, m2 = minus
    if dimension == 8:
        conditions = [coefficient(p1_scaled, -2), coefficient(p2_scaled, -2),
                      coefficient(p2_scaled, 0), coefficient(m2, -1),
                      coefficient(f-m0, -2)]
    else:
        conditions = [coefficient(p1_scaled, -4), coefficient(p2_scaled, -4),
                      coefficient(p2_scaled, -2), coefficient(p2_scaled, 0),
                      coefficient(m2, -3), coefficient(m2, -1),
                      coefficient(f-m0, -4)]
    matrix, rhs = sp.linear_eq_to_matrix(conditions, variables)
    assert matrix == expected
    assert rhs == sp.zeros(len(conditions), 1)
    assert matrix*witness == sp.zeros(len(conditions), 1)
    assert matrix.rank() == len(variables)-1

    substitution = dict(zip(variables, witness))
    # A1 = i*a1, a1=delta*p1_scaled, lambda=[q^0]A1/4.
    # Consequently lambda/pi = -[q^0]p1_scaled/2.
    lambda_over_pi = -coefficient(p1_scaled, 0).subs(substitution)/2
    assert lambda_over_pi == expected_lambda_over_pi
    scale = lambda_over_pi*sp.pi
    finite_a0 = lambda exp: sp.simplify(coefficient(f+m0, exp).subs(substitution)/scale)
    finite_a1 = lambda exp: sp.simplify(-2*sp.pi*coefficient(p1_scaled, exp).subs(substitution)/scale)
    assert finite_a1(0) == 4
    if dimension == 8:
        assert finite_a0(-2) == -1/(30*sp.pi)
        assert finite_a0(0) == -54/(5*sp.pi)
    else:
        assert finite_a0(-4) == -1/(16380*sp.pi)
        assert finite_a0(-2) == -292/(4095*sp.pi)
        assert finite_a0(0) == -14347/(1365*sp.pi)
        assert finite_a1(-2) == sp.Rational(1, 39)
    print(f"d={dimension}: shape={matrix.shape}, rank={matrix.rank()}, "
          f"lambda={lambda_over_pi}*pi; all cusp and finite-coefficient checks passed")
    print("Cusp matrix:")
    print(matrix)
    print("Rational witness:")
    print(witness.T)


if __name__ == "__main__":
    check_covariants()
    print("Theta covariant polynomial identities passed")
    check_six_by_six_relations()
    print("Six-component rational group relations and block splitting passed")
    check_derivative_blocks()
    print("Ordinary-derivative block identities passed")
    check_dimension(8)
    check_dimension(24)
