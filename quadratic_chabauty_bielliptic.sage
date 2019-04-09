"""r
Quadratic Chabauty for bielliptic curves over `\QQ` of genus `2`, rank `2`.

Code for bielliptic curves computations of [Bia19]. See also [BD18].
The main function is `quadratic_chabauty_bielliptic`. See its docstring
for details on input and output and for more examples.


REFERENCES:

- [Bia19] \F. Bianchi, "Quadratic Chabauty for (bi)elliptic curves
  and Kim's conjecture".

- [BD18] \J.S. Balakrishnan and N. Dogra, "Quadratic Chabauty and
  rational points I: p-adic heights", Duke Math. J, 2018.


EXAMPLES::

Wetherell's curve ([Bia19, Example 6.3])::

    sage: R.<x> = PolynomialRing(QQ)
    sage: f = x^6 + x^2 + 1
    sage: rat_points, other_points = quadratic_chabauty_bielliptic(f, 3, 30)
    Omega1 has 2 elements
    Omega2 has 2 elements
    Omega1 is [2*3 + 2*3^2 + 3^5 + 3^6 + 2*3^8 + 3^9 + 2*3^10 + 3^12 + 2*3^13 + 3^14 + 2*3^16 + 2*3^17 + O(3^19), O(3^19)]
    Omega2 is [2*3 + 3^3 + 2*3^4 + O(3^7), 3 + 2*3^3 + 2*3^4 + 3^5 + 3^6 + O(3^7)]
    Note: there are some finite Weierstrass disks! Beware of precision!
    Note: there are some finite Weierstrass disks! Beware of precision!
    sage: print rat_points
    [(-1/2 : -9/8 : 1), (-1/2 : 9/8 : 1), (0 : -1 : 1), (0 : 1 : 0), (0 : 1 : 1), (1/2 : -9/8 : 1), (1/2 : 9/8 : 1)]
    sage: print len(other_points)
    4

The modular curve `X_0(91)^+`::

    sage: R.<x> = PolynomialRing(QQ)
    sage: f = x^6 - 3*x^4 + 19*x^2 - 1
    sage: p = 5
    sage: n = 40
    sage: rat_points, other_points = quadratic_chabauty_bielliptic(f, p, n)
    Omega1 has 1 elements
    Omega2 has 1 elements
    Omega1 is [O(5^38)]
    Omega2 is [O(5^38)]
    sage: print rat_points
    [(-1 : -4 : 1), (-1 : 4 : 1), (-1/3 : -28/27 : 1), (-1/3 : 28/27 : 1), (0 : 1 : 0), (1/3 : -28/27 : 1), (1/3 : 28/27 : 1), (1 : -4 : 1), (1 : 4 : 1)]
    sage: print len(other_points)
    8

AUTHORS:

- FRANCESCA BIANCHI (started: July 2018; this version: March 2019). Note that some parts of the code are taken and modified from JENNIFER BALAKRISHNAN and NETAN DOGRA's code,   available at:

  https://github.com/jbalakrishnan/QCI/blob/master/Ex1.sage


"""


############## AUXILIARY FUNCTIONS ##############

import itertools
import sage.schemes.hyperelliptic_curves.monsky_washnitzer as monsky_washnitzer


def has_potential_good_reduction(H, p):
    r"""
    Return `True` if `H` has potential good reduction at `p` and `False` otherwise.

    INPUT:

    - ``H`` -- a hyperelliptic curve over `\QQ` of genus `2`.

    - ``p`` -- a prime.

    OUTPUT: Boolean.

    EXAMPLES:

    The modular curve `X_0(91)^+`::

        sage: R.<x> = PolynomialRing(QQ)
        sage: f = x^6 - 3*x^4 + 19*x^2 - 1
        sage: H = HyperellipticCurve(f)
        sage: f.discriminant().factor()
        2^22 * 7^2 * 13^2
        sage: has_potential_good_reduction(H,2)
        True
        sage: has_potential_good_reduction(H,7)
        False
        sage: has_potential_good_reduction(H,13)
        False
    """
    pol_0, pol_1 = H.hyperelliptic_polynomials()
    R = genus2reduction(pol_1, pol_0)
    try:
        if '(I)' in R.local_data[p]:
            return True
        else:
            return False
    except KeyError:
        return True


def non_archimedean_local_height(P, v, p, prec, weighted=False, is_minimal=None):
    """r
    Return the local `p`-adic height of `P` at the place `v`.
    This is a modified version of the built-in function `non_archimedean_local_height`:
    the symbolic logarithm (or real logarithm) is replaced by the `p`-adic logarithm.

    INPUT:

    - ``P`` -- a point on an elliptic curve over a number field `K`.

    - ``v`` -- a non-archimedean place of `K`` or `None`.

    - ``p`` -- an odd prime.

    - ``prec`` -- integer. The precision of the computation.

    - ``weighted`` -- boolean. If False (default), the height is
      normalised to be invariant under extension of `K`. If True,
      return this normalised height multiplied by the local degree.

    OUTPUT:

    A p-adic number: the `v`-adic component of the `p`-adic height of `P`
    if `v` is a place; the sum of the components away from `p` of the
    `p`-adic height of `P` if `v` is `None`.
    """
    if v is None:
        D = P.curve().discriminant()
        K = P.curve().base_ring()
        if K is QQ:
            factorD = D.factor()
            if P[0] == 0:
                c = 1
            else:
                c = P[0].denominator()
            # The last sum is for bad primes that divide c where
            # the model is not minimal.
            h = (log(Qp(p, prec)(c))
                 + sum(non_archimedean_local_height(P, q, p, prec, weighted=True, is_minimal=(e < 12))
                       for q,e in factorD if not q.divides(c))
                 + sum(non_archimedean_local_height(P, q, p, prec, weighted=True)
                       - c.valuation(q) * log(Qp(p, prec)(q))
                       for q,e in factorD if e >= 12 and q.divides(c)))
        else:
            factorD = K.factor(D)
            if P[0] == 0:
                c = K.ideal(1)
            else:
                c = K.ideal(P[0]).denominator()
            # The last sum is for bad primes that divide c where
            # the model is not minimal.
            h = (log(Qp(p, prec)(c.norm()))
                 + sum(non_archimedean_local_height(P, v, p, prec, weighted=True, is_minimal=(e < 12))
                       for v,e in factorD if not v.divides(c))
                 + sum(non_archimedean_local_height(P, v, p, prec, weighted=True)
                       - c.valuation(v) * log(Qp(p, prec)(v.norm()))
                       for v,e in factorD if e >= 12 and v.divides(c)))
            if not weighted:
                h /= K.degree()
        return h

    if is_minimal:
        E = P.curve()
        offset = ZZ.zero()
        Pmin = P
    else:
        E = P.curve().local_minimal_model(v)
        Pmin = P.curve().isomorphism_to(E)(P)
        # Silverman's normalization is not invariant under change of model,
        # but it all cancels out in the global height.
        offset = (P.curve().discriminant()/E.discriminant()).valuation(v)

    a1, a2, a3, a4, a6 = E.a_invariants()
    b2, b4, b6, b8 = E.b_invariants()
    c4 = E.c4()
    x, y = Pmin.xy()
    D = E.discriminant()
    N = D.valuation(v)
    A = (3*x**2 + 2*a2*x + a4 - a1*y).valuation(v)
    B = (2*y+a1*x+a3).valuation(v)
    C = (3*x**4 + b2*x**3 + 3*b4*x**2 + 3*b6*x + b8).valuation(v)
    if A <= 0 or B <= 0:
        r = max(0, -x.valuation(v))
    elif c4.valuation(v) == 0:
        n = min(B, N/2)
        r = -n*(N-n)/N
    elif C >= 3*B:
        r = -2*B/3
    else:
        r = -C/4
    r -= offset/6
    if not r:
        return Qp(p,prec)(0)
    else:
        if E.base_ring() is QQ:
            Nv = Integer(v)
        else:
            Nv = v.norm()
            if not weighted:
                r = r / (v.ramification_index() * v.residue_class_degree())
        return r * log(Qp(p,prec)(Nv))


def coleman_integrals_on_basis(H, P, Q, inverse_frob, forms, algorithm=None):
    r"""
    Compute the Coleman integrals `\{\int_P^Q x^i dx/2y \}_{i=0}^{2g-1}`.
    The only difference with the built-in function coleman_integrals_on_basis
    is that we input the Frobenius data `(inverse_frob, forms)`.

    INPUT:

    - ``H`` -- a hyperelliptic curve over a `p`-adic field `K`.

    - ``P`` -- a point on `H`.

    - ``Q`` -- a point on `H`.

    - ``inverse_frob`` -- `(M_frob^T-1)^(-1)` where `M_frob` is the matrix of Frobenius
      on Monsky-Washnitzer cohomology, with respect to the basis `(dx/2y, x dx/2y, ...x^{d-2} dx/2y)`
      and with coefficients in `K`.

    - ``forms`` -- list of differentials `\{f_i\}` such that
      `\phi^* (x^i dx/2y) = df_i + M_frob[i]*vec(dx/2y, ..., x^{d-2} dx/2y)`;
      the coefficients of the `f_i` should be in `K`.

    - ``algorithm`` (optional) --  None (uses Frobenius) or teichmuller
      (uses Teichmuller points).

    OUTPUT:

    The Coleman integrals `\{\int_P^Q x^i dx/2y \}_{i=0}^{2g-1}`.

    EXAMPLES:

    This example illustrates how to compute the data `(inverse_frob,forms)` for `H`::

        sage: import sage.schemes.hyperelliptic_curves.monsky_washnitzer as monsky_washnitzer
        sage: K = H.base_ring()
        sage: M_frob, forms = monsky_washnitzer.matrix_of_frobenius_hyperelliptic(H)
        sage: forms = [form.change_ring(K) for form in forms]
        sage: M_sys = matrix(K, M_frob).transpose() - 1
        sage: inverse_frob = M_sys**(-1)
    """
    K = H.base_ring()
    p = K.prime()
    prec = K.precision_cap()
    g = H.genus()
    dim = 2*g
    V = VectorSpace(K, dim)
    #if P or Q is Weierstrass, use the Frobenius algorithm
    if H.is_weierstrass(P):
        if H.is_weierstrass(Q):
            return V(0)
        else:
            PP = None
            QQ = Q
            TP = None
            TQ = H.frobenius(Q)
    elif H.is_weierstrass(Q):
        PP = P
        QQ = None
        TQ = None
        TP = H.frobenius(P)
    elif H.is_same_disc(P, Q):
        return H.tiny_integrals_on_basis(P, Q)
    elif algorithm == 'teichmuller':
        PP = TP = H.teichmuller(P)
        QQ = TQ = H.teichmuller(Q)
        evalP, evalQ = TP, TQ
    else:
        TP = H.frobenius(P)
        TQ = H.frobenius(Q)
        PP, QQ = P, Q
    if TP is None:
        P_to_TP = V(0)
    else:
        if TP is not None:
            TPv = (TP[0]**g/TP[1]).valuation()
            xTPv = TP[0].valuation()
        else:
            xTPv = TPv = +Infinity
        if TQ is not None:
            TQv = (TQ[0]**g/TQ[1]).valuation()
            xTQv = TQ[0].valuation()
        else:
            xTQv = TQv = +Infinity
        offset = (2*g-1)*max(TPv, TQv)
        if offset == +Infinity:
            offset = (2*g-1)*min(TPv,TQv)
        if (offset > prec and (xTPv < 0 or xTQv < 0) and (H.residue_disc(P) == H.change_ring(GF(p))(0, 1, 0) or H.residue_disc(Q) == H.change_ring(GF(p))(0, 1, 0))):
            newprec = offset + prec
            K = pAdicField(p,newprec)
            A = PolynomialRing(RationalField(),'x')
            f = A(H.hyperelliptic_polynomials()[0])
            from sage.schemes.hyperelliptic_curves.constructor import HyperellipticCurve
            H = HyperellipticCurve(f).change_ring(K)
            xP = P[0]
            xPv = xP.valuation()
            xPnew = K(sum(c * p**(xPv + i) for i, c in enumerate(xP.expansion())))
            PP = P = H.lift_x(xPnew)
            TP = H.frobenius(P)
            xQ = Q[0]
            xQv = xQ.valuation()
            xQnew = K(sum(c * p**(xQv + i) for i, c in enumerate(xQ.expansion())))
            QQ = Q = H.lift_x(xQnew)
            TQ = H.frobenius(Q)
            V = VectorSpace(K,dim)
        P_to_TP = V(H.tiny_integrals_on_basis(P, TP))
    if TQ is None:
        TQ_to_Q = V(0)
    else:
        TQ_to_Q = V(H.tiny_integrals_on_basis(TQ, Q))
    if PP is None:
        L = [-f(QQ[0], QQ[1]) for f in forms]  ##changed
    elif QQ is None:
        L = [f(PP[0], PP[1]) for f in forms]
    else:
        L = [f(PP[0], PP[1]) - f(QQ[0], QQ[1]) for f in forms]
    b = V(L)
    if PP is None:
        b -= TQ_to_Q
    elif QQ is None:
        b -= P_to_TP
    elif algorithm != 'teichmuller':
        b -= P_to_TP + TQ_to_Q
    #M_sys = matrix(K, M_frob).transpose() - 1
    TP_to_TQ = inverse_frob * b
    if algorithm == 'teichmuller':
        return P_to_TP + TP_to_TQ + TQ_to_Q
    else:
        return TP_to_TQ


def Q_lift(CK, Q, p):
    r"""
    Compute the Teichmueller point lifting a given point over `GF(p)`.

    INPUT:

    - ``CK`` -- a hyperelliptic curve over `\QQ_p`.

    - ``Q`` -- a point in `CK(GF(p))`.

    - ``p`` -- the prime of the first two input items.

    OUTPUT: The point on `CK` lifting `Q` and fixed by Frobenius.
    """
    xQ = Integers()(Q[0])
    yQ = Integers()(Q[1])
    if yQ == 0:
        r = CK.hyperelliptic_polynomials()[0].roots()
        Q_lift = CK(exists(r, lambda a : (Integers()(a[0])-xQ) % p == 0)[1][0],0)
    else:
        K = CK.base_ring()
        xQ = K.teichmuller(K(xQ))
        lifts = CK.lift_x(xQ, all=True)
        for i in range(len(lifts)):
            if (Integers()(lifts[i][1])-yQ) % p == 0:
                Q_lift = lifts[i]
    return Q_lift


def embeddings(K, p, prec):
    """r
    Compute the embedding(s) of `K` in the completions of `K` at
    the primes above `p`. This is taken from the code used for [BcL+16].

    INPUT:

    - ``K`` -- a quadratic field.

    - ``p`` -- a prime.

    - ``prec`` -- the `p`-adic precision.

    OUTPUT:
    A list of embeddings of `K` in `\QQ_p` if `p` splits in `K`;
    an embedding of `K =\QQ(\sqrt(D))` in `\QQ_p(\sqrt(D))` otherwise.

    REFERENCES:

    - [BcL+16] \J. S. Balakrishnan, M. Ciperiani, J. Lang, B. Mirza, and R. Newton, "Shadow
      lines in the arithmetic of elliptic curves". In" Directions in number theory, volume 3".
    """
    Q = pAdicField(p,prec)
    OK = K.maximal_order()
    pOK = factor(p*OK)
    if (len(pOK) == 2 and pOK[0][1] == 1):
        R = Q['x']
        r1, r2 = R(K.defining_polynomial()).roots()
        psi1 = K.hom([r1[0]])
        psi2 = K.hom([r2[0]])
        return [psi1, psi2]
    else:
        F = Q.extension(K.defining_polynomial(),names='a')
        a = F.gen()
        psi = self._psis = [K.hom([a])]
        return psi


############## Functions from [BD18] ##############

r""""
The following functions (until specified) are from the github code for [BD18]:

https://github.com/jbalakrishnan/QCI/blob/master/Ex1.sage

with some changes. The bielliptic curve there is assumed to have `a0 = 1`;
here we allow for arbitrary `a0`.
"""

def X_to_E1map(Xpt, E1):
    if Xpt[2] == 0:
        pass
    else:
        x, y, _ = Xpt
        return E1(x^2, y)


def X_to_E2map(Xpt, E2, a0):
    if Xpt[2] == 0:
        return E2(0, a0)
    else:
        x,y,_ = Xpt
        if x !=0:
            return E2(a0*x^-2, a0*y*x^-3)
        else:
            return E2(0, 1, 0)


def X_to_E2map_plus(Xpt, E2, a0):
    if Xpt[2] == 0:
        pass
    else:
        x, y, _ = Xpt
        if x !=0:
            return E2(a0*x^-2, a0*y*x^-3) + E2(0, a0)
        else:
            return E2(0, 1, 0) +E2(0, a0)


def X_to_E2map_minus(Xpt, E2, a0):
    if Xpt[2] == 0:
        pass
    else:
        x, y, _ = Xpt
        if x !=0:
            return E2(a0*x^-2, a0*y*x^-3) - E2(0, a0)
        else:
            return E2(0, 1 ,0) - E2(0, a0)


def X_to_E1map_plus(Xpt, E1, a0):
    K = E1.base_ring()
    if Xpt[2] == 0:
        return E1((0, K(a0).sqrt()))#QQ(a0.sqrt())))
    else:
        x, y, _ = Xpt
        return E1(x^2, y) + E1.lift_x(0, all=True)[0] #FB changed this from E1.lift_x((0,1))


def X_to_E1map_minus(Xpt, E1, a0):
    K = E1.base_ring()
    if Xpt[2] == 0:
        return  E1(0, -K(a0).sqrt())#-QQ(a0.sqrt()))
    else:
        x, y, _ = Xpt
        return  E1(x^2, y) + E1.lift_x(0, all=True)[1] #FB changed this from E1.lift_x((0,1))


def param_f2Xplus(x, y, E2K, a0):
    """r
    Return the coordinates of `f_2(z) + (0,a0)` in terms of the local coordinate with
    respect to which `z = (x,y)`.
    """
    x1 = a0*x^-2
    x2 = 0
    y1 = a0*x^-3*y
    y2 = a0
    a = E2K.a2()
    lam = (y1-y2)/(x1-x2)
    mu = (y1*x2-y2*x1)/(x2-x1)
    x3 = lam^2 - a - x1 - x2
    y3 = -lam*x3 - mu
    return x3, y3


def param_f2Xmin(x, y, E2K, a0):
    """r
    Return the coordinates of `f_2(z) - (0,a0) = f_2(z) + (0,-a0)` in terms of the
    local coordinate with respect to which `z = (x,y)`.
    """
    x1 = a0*x^-2
    x2 = 0
    y1 = a0*x^-3*y
    y2 = -a0
    a = E2K.a2()
    lam = (y1-y2)/(x1-x2)
    mu = (y1*x2-y2*x1)/(x2-x1)
    x3 = lam^2 - a - x1 - x2
    y3 = -lam*x3 - mu
    return x3, y3


def param_f1(x, y):
    """r
    Return the coordinates of `f_1(z)` in terms of the local coordinate with respect
    to which `z = (x,y)`.
    """
    return x^2, y


def param_f2(x, y, a0):
    """r
    Return the coordinates of `f_2(z)` in terms of the local coordinate with respect
    to which `z = (x,y)`.
    """
    return a0*x^-2, a0*y*x^(-3)


def param_f1Xplus(x, y, E1K, p, prec, a0):
    r"""
    Return the coordinates of `f_1(z) + (0,\sqrt(a0))` in terms of the local coordinate
    with respect to which `z = (x,y)`.
    """
    x1 = x^2
    y1 = y
    x2 = 0
    y2 = Qp(p,prec)(a0).sqrt()#(QQ(a0.sqrt()))
    if y1.valuation() < 0:
        Kt.<t> = LaurentSeriesRing(Qp(p,prec))
    else:
        pass
    a = E1K.a2()
    try:
        lam = (y1-y2)/(x1-x2)
        mu =  y2
    except TypeError:
        y1 = Kt(y1)
        x1 = Kt(x1)
        lam = Kt((y1-y2)/(x1-x2))
        mu = Kt(y2)
        a = Kt(a)
    x3 = lam^2 - a - x1 - x2
    y3 = -lam*x3 - mu
    return x3, y3


def param_f1Xmin(x, y, E1K, p, prec, a0):
    r"""
    Return the coordinates of `f_1(z) + (0,-\sqrt(a0))` in terms of the local coordinate
    with respect to which `z = (x,y)`.
    """
    x1 = x^2
    y1 = y
    x2 = 0
    y2 = -Qp(p,prec)(a0).sqrt()#QQ(a0.sqrt())
    if y1.valuation() < 0:
        Kt.<t> = LaurentSeriesRing(Qp(p,prec))
    else:
        pass
    a = E1K.a2()
    try:
        lam = (y1-y2)/(x1-x2)
        mu =  y2
    except TypeError:
        y1 = Kt(y1)
        x1 = Kt(x1)
        a = Kt(a)
        lam = Kt((y1-y2)/(x1-x2))
        mu =  Kt(y2)
    x3 = lam^2 - a - x1 - x2
    y3 = -lam*x3 - mu
    return x3, y3

############## End of functions from [BD18] ##############


def local_coordinates_at_infinity_new(H, prec = 20, name = 't'):
    """r
    Return local coordinates at infinity on `H`.
    This is the same as the built-in function `local_coordinates_at_infinity`
    with a few changes, as it was giving bugs.
    """
    g = H.genus()
    pol = H.hyperelliptic_polynomials()[0]
    K = LaurentSeriesRing(H.base_ring(), name,prec+2)
    t = K.gen()
    #K.set_default_prec(prec+2)
    L = PolynomialRing(H.base_ring(),'x')
    x = L.gen()
    i = 0
    NR = PolynomialRing(K,"x")
    w = (NR(x)**g/NR(t))**2-NR(pol)
    #w = (x**g/t)**2-pol
    wprime = w.derivative(x)
    if pol.degree() == 2*g+1:
        x = t**-2
    else:
        x = t**-1
    for i in range((RR(log(prec+2)/log(2))).ceil()):
        x = x-w(x)/wprime(x)
    y = x**g/t
    return x+O(t**(prec+2)) , y+O(t**(prec+2))


def bernardi_sigma_function(E, prec=20):
    r"""
     Return the sigma function of Bernardi in terms of `z = log(t)`.
    This is an adaptation of the code built in sage. The difference is that we input
    the curve instead of the `L`-function and that we are adding `r` to `xofF`.

    INPUT:

    - ``E`` -- an elliptic curve over `\QQ`.

    - ``prec`` -- power series precision.

    OUTPUT: A power series in `z` with coefficients in \QQ approximating the sigma function
    of Bernardi.

    .. NOTE::

        This will converge on some `p`-adic neighbourhood of the identity on `E`
        for a prime `p` of good reduction.
    """
    Eh = E.formal()
    lo = Eh.log(prec + 5)
    F = lo.reverse()

    S = LaurentSeriesRing(QQ,'z',default_prec = prec)
    z = S.gen()
    F = F(z)
    xofF = Eh.x(prec + 2)(F)
    r =  ( E.a1()**2 + 4*E.a2() ) / ZZ(12)
    xofF = xofF + r
    g = (1/z**2 - xofF ).power_series()
    h = g.integral().integral()
    sigma_of_z = z.power_series() * h.exp()

    return sigma_of_z


def height_bernardi(P, p, prec):
    """r
    Return the `p`-adic height of Bernardi at `P`.

    INPUT:

    - ``P`` -- a point on an elliptic curve `E` over `\QQ`.

    - ``p`` -- an odd prime of good reduction for `E`.

    - ``prec`` -- integer. The precision of the computation.

    OUTPUT:
    A `p`-adic number; the Bernardi `p`-adic height of `P`.
    """
    E = P.scheme()
    tam = E.tamagawa_numbers()
    tam.append(E.Np(p))
    m = lcm(tam)
    Q = m*P
    dQ = ZZ(Q[0].denominator().sqrt())
    sigma = bernardi_sigma_function(E,prec=prec+5)
    sigma = sigma(E.formal().log(prec+5))
    sigmaQ = Qp(p, prec)(sigma(-Qp(p,prec+5)(Q[0]/Q[1])))
    return (-2*log(sigmaQ/dQ))/m^2


def local_heights_at_bad_primes_new(E, Enonmin, K):
    """r
    Compute the set of primes `q` at which `W_q` is larger than `\{0\}`
    for `Enonmin` and `W_q` for such primes (up to a translation).
    See Lemma 6.4 of [Bia19].

    INPUT:

    - ``E`` -- a minimal model for `Enonmin` over `\QQ`.

    - ``Enonmin`` -- an elliptic curve over `\QQ`.

    - ``K`` -- a `p`-adic field, where `Enonmin` has good reduction
      at `p`.

    OUTPUT:

    A tuple consisting of:

    - A list `L` of all the primes `q` at which the local heights on
      `q`-adically integral points of `Enonmin` can be different from `0`.

    - A list of lists: the `i^th` list is `W_{L[i]} - 1/6* log|\Delta_{Enonmin}/\Delta_{E}|_q`.
    """
    bad_primes = E.base_ring()(E.integral_model().discriminant()).support()
    delta = Enonmin.discriminant()/E.discriminant()
    factors_delta = [f[0] for f in delta.factor()]
    W = []
    bad_primes_new = []
    for q in bad_primes:
        if E.tamagawa_number(q) == 1:
            continue
        bad_primes_new.append(q)
        ks = E.kodaira_symbol(q)
        if E.has_additive_reduction(q):
            if ks == KodairaSymbol(3): #III
                W.append([-1/2*(K(q)).log()])
            elif ks == KodairaSymbol(4): #IV
                W.append([-2/3*K(q).log()])
            elif ks == KodairaSymbol(-1): #I0*
                W.append([-K(q).log()])
            elif ks == KodairaSymbol(-4): #IV*
                W.append([-(4/3)*K(q).log()])
            elif ks == KodairaSymbol(-3): #III*
                W.append([-(3/2)*K(q).log()])
            else: #Im*
                if E.tamagawa_number(q) == 2:
                    W.append([-K(q).log()])
                else:
                    n = -5
                    while ks != KodairaSymbol(n):
                        n = n-1
                    m = -n-4
                    W.append([-K(q).log(), -(m+4)/4*K(q).log()])
        else: #multiplicative
            n = 5
            while ks != KodairaSymbol(n):
                n = n+1
            m = n-4
            if E.tamagawa_number(q) == 2:
                W.append([-m/4*K(q).log()])
            else:
                W.append([-i*(m-i)/m*(K(q)).log() for i in range(1, (m/2).floor() + 1)])

    for j in range(len(W)):
        q = bad_primes_new[j]
        if q == 2:
            if E.has_split_multiplicative_reduction(q):
                continue
        W[j] = [0] + W[j]
        if delta.valuation(q) > 0:
            W[j] = list(Set(W[j] + [2*K(k)*K(q).log() for k in range(1, ZZ(delta.valuation(q)/12) + 1)]))

    bad_primes_new_new = bad_primes_new

    for q in factors_delta:
        if q not in bad_primes:
            if q == 2 and E.Np(2) == 1 or q == 3 and E.Np(3) == 1:
                W.append([2*K(k)*K(q).log() for k in range(1, ZZ(delta.valuation(q)/12) + 1)])
            else:
                W.append([2*K(k)*K(q).log() for k in range(0, ZZ(delta.valuation(q)/12) + 1)])
            bad_primes_new_new.append(q)

    return bad_primes_new_new, W


############## MAIN FUNCTION ###############


def quadratic_chabauty_bielliptic(f, p, n, Omega1=[], Omega2=[], bernardi=False, potential_good_primes=True):
    """r
    Do quadratic Chabauty on a genus `2` bielliptic curve of rank `2`.
    WARNING: Some bits of this code were taken (and modified) from the code used for [BD18].

    INPUT:

    - ``f`` -- a polynomial over `\QQ` of the form `x^6 + a_4*x^4 + a_2*x^2 + a_0`,
      `a_i \in \ZZ`. The two elliptic curves `E_1` and `E_2` should have rank `1`.
      If `Omega1` and `Omega2` are not provided, `a_0` should be square-free.

    - ``p`` -- an odd prime of good reduction for `H: y^2 = f(x)`.

    - ``n`` -- working `p`-adic precision.

    - ``Omega1`` and ``Omega2`` -- lists of the values in `Omega1` and `Omega2` from [BD18]
      (`W^1` and `W^2` in the notation of [Bia19]), but with respect to minimal models for the
      elliptic curves (i.e. they equal the ones of [BD18] only up to a translation).
      This is because in this code the heights are computed wrt minimal models. If not provided,
      finite sets containing `Omega1` and `Omega2` are calculated (see [Bia19]).

    - ``bernardi`` -- True/False (default False): if False and `p` is and `\ge 5` and ordinary for
      the elliptic curves corresponding to `H`, the Mazur-Tate sigma function is used; otherwise, the Bernardi one.

    - ``potential_good_primes`` -- True/False (default True): if True, and ``Omega1`` and ``Omega2``
      are not provided, it uses the fact that the contributions at the primes of potential good reduction
      for `H` are trivial (i.e. the sets `W^{i\prime\prime}` of [Bia19] are used); otherwise, the sets
      `W^{i\prime}` are used.

    OUTPUT: A tuple consisting of:

    - A sorted list of rational points on `H`.

    - A sorted list of `p`-adic points on `H` which have not been recognised as rational points.

    .. NOTE::

        If `Omega1` and `Omega2` are not provided, the size and elements of `W^{i\prime\prime}`
        (or `W^{i\prime}` if `potential_good_primes` is `False`) are printed. The print statement
        imprecisely refers to those sets as  `Omega1` and  `Omega2`, but they could be larger.


    EXAMPLES:

    Example 2 (8.4) of [BD18] but over `\QQ`::

        sage: R.<x> = PolynomialRing(QQ)
        sage: f = x^6 - 9*x^4 + 11*x^2 + 37
        sage: p = 7
        sage: n = 15
        sage: K = Qp(p, n)
        sage: Omega1 = [4*log(K(2)) + 4/3*log(K(37))]
        sage: Omega2 =  [-2/3*log(K(37)) - 4*log(K(2))]
        sage: rat_points, other_points = quadratic_chabauty_bielliptic(f, p, n, Omega1=Omega1, Omega2=Omega2)
        sage: rat_points
        [(-2 : -1 : 1), (-2 : 1 : 1), (0 : 1 : 0), (2 : -1 : 1), (2 : 1 : 1)]
        sage: other_points
        [(5 + 6*7^2 + 6*7^4 + 7^5 + 4*7^6 + 6*7^7 + 3*7^8 + O(7^10) : 6 + 7 + 3*7^2 + 4*7^4 + 2*7^5 + 6*7^6 + 3*7^7 + 5*7^8 + 7^9 + O(7^10) : 1 + O(7^15)),
         (5 + 6*7^2 + 6*7^4 + 7^5 + 4*7^6 + 6*7^7 + 3*7^8 + O(7^10) : 1 + 5*7 + 3*7^2 + 6*7^3 + 2*7^4 + 4*7^5 + 3*7^7 + 7^8 + 5*7^9 + O(7^10) : 1 + O(7^15)),
         (2 + 6*7 + 6*7^3 + 5*7^5 + 2*7^6 + 3*7^8 + 6*7^9 + O(7^10) : 6 + 7 + 3*7^2 + 4*7^4 + 2*7^5 + 6*7^6 + 3*7^7 + 5*7^8 + 7^9 + O(7^10) : 1 + O(7^15)),
         (2 + 6*7 + 6*7^3 + 5*7^5 + 2*7^6 + 3*7^8 + 6*7^9 + O(7^10) : 1 + 5*7 + 3*7^2 + 6*7^3 + 2*7^4 + 4*7^5 + 3*7^7 + 7^8 + 5*7^9 + O(7^10) : 1 + O(7^15))]

    Same example but not providing `Omega1` and `Omega2`::

        sage: rat_points, other_points = quadratic_chabauty_bielliptic(f, p, n)
        Omega1 has 3 elements
        Omega2 has 3 elements
        Omega1 is [6*7 + 7^2 + 4*7^3 + 3*7^4 + 5*7^5 + 3*7^6 + 6*7^7 + 6*7^8 + 3*7^9 + 7^10 + 7^11 + O(7^13), 6*7^2 + 5*7^4 + 5*7^5 + 3*7^6 + 2*7^7 + 5*7^8
        + 4*7^9 + 4*7^10 + 4*7^11 + 4*7^12 + O(7^13), 2*7 + 2*7^2 + 4*7^3 + 4*7^4 + 5*7^5 + 3*7^6 + 7^7 + 7^8 + 2*7^9 + 7^10 + 7^11 + 3*7^12 + O(7^13)]
        Omega2 is [6*7 + 7^2 + 6*7^3 + 3*7^4 + 7^5 + 3*7^6 + 7^7 + 4*7^8 + 5*7^9 + 7^10 + O(7^11), 5*7 + 4*7^2 + 2*7^3 + 2*7^4 + 7^5 + 3*7^6 + 5*7^7 + 5*7^8
        + 4*7^9 + 5*7^10 + O(7^11), 3*7 + 7^2 + 6*7^3 + 2*7^4 + 7^5 + 3*7^6 + 6*7^7 + 2*7^8 + 2*7^10 + O(7^11)]
        sage: rat_points
        [(-2 : -1 : 1), (-2 : 1 : 1), (0 : 1 : 0), (2 : -1 : 1), (2 : 1 : 1)]
        sage: len(other_points)
        10


    """
    prec = n
    H = HyperellipticCurve(f)
    a4 = f[4]
    a2 = f[2]
    a0 = f[0]
    E1 = EllipticCurve([0, a4, 0, a2, a0])
    E2 = EllipticCurve([0, a2, 0, a4*a0, a0^2])
    if p == 3:
        bernardi = True
    if E1.is_ordinary(p) == False or E2.is_ordinary(p) == False:
        bernardi = True
    H1 = HyperellipticCurve(x^3 + a4*x^2 + a2*x + a0)
    H2 = HyperellipticCurve(x^3 + a2*x^2 + a4*a0*x + a0^2)
    K = Qp(p, n)
    assert len(PolynomialRing(K, "x")(x^2 - a0).roots()) == 2, "The square-root of a0 is not defined in Qp"
    sqrta0K = PolynomialRing(K, "x")(x^2 - a0).roots()[0][0]

    #Step 1: computing minimimal models of E1, E2 and isomorphisms to and from them,
    #generators of E1(Q), E2(Q) and their heights:
    E1min = E1.minimal_model()
    E2min = E2.minimal_model()
    delta1 = E1.discriminant()/E1min.discriminant()
    delta2 = E2.discriminant()/E2min.discriminant()
    phi1 = E1.isomorphism_to(E1min)
    psi1 = E1min.isomorphism_to(E1)
    [u1, r1, s1, tt1] = psi1.tuple()
    phi2 = E2.isomorphism_to(E2min)
    psi2 = E2min.isomorphism_to(E2)
    [u2, r2, s2, tt2] = psi2.tuple()
    P1min = E1min.gens()[0]
    P2min = E2min.gens()[0]
    if bernardi == False:
        h1 = E1min.padic_height(p, n)
        h2 = E2min.padic_height(p, n)
        hP1 = h1(P1min)
        hP2 = h2(P2min)
    else:
        hP1 = height_bernardi(P1min, p, n)
        hP2 = height_bernardi(P2min, p, n)
    P1 = psi1(P1min)
    P2 = psi2(P2min)
    H1K = H1.change_ring(K)
    H2K = H2.change_ring(K)
    HK = H.change_ring(K)
    E1K = E1.change_ring(K)
    E2K = E2.change_ring(K)

    #Compute Frobenius data only once:
    M1_frob, forms1 = monsky_washnitzer.matrix_of_frobenius_hyperelliptic(H1K)
    forms1 = [form.change_ring(K) for form in forms1]
    M_sys1 = matrix(K, M1_frob).transpose() - 1
    inverse_frob1 = M_sys1**(-1)
    M2_frob, forms2 = monsky_washnitzer.matrix_of_frobenius_hyperelliptic(H2K)
    forms2 = [form.change_ring(K) for form in forms2]
    M_sys2 = matrix(K, M2_frob).transpose() - 1
    inverse_frob2 = M_sys2**(-1)

    logE2_a0K = coleman_integrals_on_basis(H2K, H2K(0, 1, 0), H2K(0, a0), inverse_frob2, forms2)[0]
    alpha1 = hP1/coleman_integrals_on_basis(H1K, H1K(0, 1, 0), H1K(P1[0], P1[1]), inverse_frob1, forms1)[0]^2
    alpha2 = hP2/coleman_integrals_on_basis(H2K, H2K(0, 1, 0), H2K(P2[0], P2[1]), inverse_frob2, forms2)[0]^2

    Hp = H.change_ring(GF(p))
    Hppoints = Hp.points()
    D = Hppoints[:]
    sqrta0ps = PolynomialRing(GF(p), "x")(x^2 - a0).roots()
    D.remove(Hp(0, sqrta0ps[0][0]))
    D.remove(Hp(0, sqrta0ps[1][0]))
    D0 = [Hp(0, sqrta0ps[0][0]), Hp(0, sqrta0ps[1][0])]
    #Change to this definition of D0 to check that the points recovered are independent of the patch
    #D0 = Hppoints[:]
    #D0.remove(Hp(0, 1, 0))
    #D = [Hp(0, 1, 0)]

    m1 = E1min.Np(p)
    m2 = E2min.Np(p)
    if bernardi == False:
        sigma1 = E1min.padic_sigma(p, n)
        sigma2 = E2min.padic_sigma(p, n)
        val_sigma1 = 0
        val_sigma2 = 0
        val_sigma = 0
    else:
        sigma1 =  bernardi_sigma_function(E1min, prec=n)
        sigma1 = sigma1(E1min.formal().log(n))
        sigma2 =  bernardi_sigma_function(E2min, prec=n)
        sigma2 = sigma2(E2min.formal().log(n))
        val_sigma1 = max(sigma1[i].denominator().valuation(p) for i in range(sigma2.precision_absolute()))
        val_sigma2 = max(sigma2[i].denominator().valuation(p) for i in range(sigma2.precision_absolute()))
        val_sigma = max(val_sigma1, val_sigma2) #this will be used to readjust the p-adic precision of sigma
        #Disclaimer: have not checked that the precision we use give provable outputs.

    if m1 % 2 != 0:
        fm1 = E1min.division_polynomial(m1)
    else:
        fm1 = E1min.division_polynomial(m1, two_torsion_multiplicity=1)

    if m2 % 2 != 0:
        fm2 = E2min.division_polynomial(m2)
    else:
        fm2 = E2min.division_polynomial(m2, two_torsion_multiplicity=1)

    #Local height at p and global height of Q2:
    Q2 = E2(0, a0)
    Q2min = phi2(Q2)
    mQ2min = m2*Q2min
    sigmamQ2min = Qp(p, prec-val_sigma2-2)(sigma2(-Qp(p, prec+5)(mQ2min[0]/mQ2min[1])))
    if m2 % 2 != 0:
        lambdapQ2 = (-2*(sigmamQ2min/fm2(Q2min[0])).log(p_branch=0))/m2^2
    else:
        lambdapQ2 = (-2*(sigmamQ2min/fm2(Q2min[0],Q2min[1])).log(p_branch=0))/m2^2
    hQ2 = alpha2*logE2_a0K^2

    #Local height at p and global height of Q1:
    if a0.is_square() == True:
        logE1_sqrta0K = coleman_integrals_on_basis(H1K, H1K(0, 1, 0), H1K(0, sqrta0K), inverse_frob1, forms1)[0]
        hQ1 = alpha1*logE1_sqrta0K^2
        Q1 = E1(0, QQ(a0.sqrt()))
        Q1min = phi1(Q1)
        mQ1min = m1*Q1min
        sigmamQ1min = Qp(p, prec-val_sigma1-2)(sigma1(-Qp(p, prec+5)(mQ1min[0]/mQ1min[1])))
        if m1 % 2 != 0:
            lambdapQ1 = (-2*(sigmamQ1min/fm1(Q1min[0])).log(p_branch=0))/m1^2
        else:
            lambdapQ1 = (-2*(sigmamQ1min/fm1(Q1min[0],Q1min[1])).log(p_branch=0))/m1^2
    else:
        Qsqrta0.<sa0> = QuadraticField(a0)
        embd = embeddings(Qsqrta0, p, prec+5)[0]
        E1_sqrta0 = E1.change_ring(Qsqrta0)
        E1min_sqrta0 = E1min.change_ring(Qsqrta0)
        Q1_sqrta0 = E1_sqrta0(0, sa0)
        Q1min_sqrta0 = E1min_sqrta0(phi1(Q1_sqrta0))
        m1Q1min_sqrta0 = m1*Q1min_sqrta0
        sigmam1Q1min = Qp(p,prec-val_sigma1-2)(sigma1(-Qp(p,prec+5)(embd(m1Q1min_sqrta0[0]/m1Q1min_sqrta0[1]))))
        if m1 % 2 != 0:
            lambdapQ1 = (-2*(sigmam1Q1min/fm1(embd(Q1min_sqrta0[0]))).log(p_branch=0))/m1^2
        else:
            lambdapQ1 = (-2*(sigmam1Q1min/fm1(embd(Q1min_sqrta0[0]), embd(Q1min_sqrta0[1]))).log(p_branch=0))/m1^2
        hQ1 = lambdapQ1 + non_archimedean_local_height(Q1min_sqrta0, None, p, prec)

    #Computing Omega1 and Omega2 if not provided
    if Omega1 == [] and Omega2 == []:
        bad_primes_1, W1 = local_heights_at_bad_primes_new(E1min, E1, K)
        bad_primes_2, W2 = local_heights_at_bad_primes_new(E2min, E2, K)
        bad_primes = list(Set(bad_primes_1 + bad_primes_2))
        Wqprimelist1 = []
        Wqprimelist2 = []
        for q in bad_primes:
            if potential_good_primes == True:
                if has_potential_good_reduction(H,q) == True:
                    if a0.is_square():
                        lambdaqQ1min = non_archimedean_local_height(Q1min, q, p, n)
                    else:
                        OQsqrta0 = Qsqrta0.ring_of_integers()
                        lambdaqQ1min = non_archimedean_local_height(Q1min_sqrta0, (q*OQsqrta0).factor()[0][0], p, n)
                    lambdaqQ2min = non_archimedean_local_height(Q2min, q, p, n)
                    Wqprime1 = [-2*lambdaqQ1min - 1/3*log(K(q^(-(delta1).valuation(q)))) + 1/3*log(K(q^(-(delta2).valuation(q))))]
                    Wqprime2 = [-2*lambdaqQ2min - 1/3*log(K(q^(-(delta2).valuation(q)))) + 1/3*log(K(q^(-(delta1).valuation(q))))]
                    Wqprimelist1.append(Wqprime1)
                    Wqprimelist2.append(Wqprime2)
                    continue

            if q in bad_primes_1:
                WE1q = W1[bad_primes_1.index(q)]
            else:
                if q == 2 and E1.Np(2) == 1:
                    WE1q = []
                elif q == 3 and E1.Np(3) == 1:
                    WE1q = []
                elif q == 2 and E1.has_split_multiplicative_reduction(2) == True and E1.kodaira_symbol(2) == KodairaSymbol(5):
                    WE1q = []
                else:
                    WE1q = [0]
            if q in bad_primes_2:
                WE2q = W2[bad_primes_2.index(q)]
            else:
                if q == 2 and E2.Np(2) == 1:
                    WE2q = []
                elif q == 3 and E2.Np(3) == 1:
                    WE2q = []
                elif q == 2 and E2.has_split_multiplicative_reduction(2) == True and E2.kodaira_symbol(2) == KodairaSymbol(5):
                    WE2q = []
                else:
                    WE2q = [0]

            #Note that the primes dividing a0 will always be prime of bad reduction for the model E2 and with at
            #least one point reducing to a singular point (0,0)s, so not missing anything
            Wqprime1 = (list(Set([-2*w2 for w2 in WE2q] +
                                 [1/3*log(K(q^(-(delta1).valuation(q)))) + 2*(w1w2[0] - w1w2[1]) for w1w2 in itertools.product(WE1q, WE2q)] +
                                 [2*w1 + 1/3*log(K(q^(-(delta1).valuation(q)))) + 1/3*log(K(q^(-(delta2).valuation(q)))) - 2*log(K(q^(-(a0).valuation(q)))) for w1 in WE1q])))
            Wqprimelist1.append(Wqprime1)
            Wqprime2 = (list(Set([2*(w2w1[0]- w2w1[1]) + 1/3*log(K(q^(-(delta2).valuation(q)))) - 2*log(K(q^(-(a0).valuation(q)))) for w2w1 in itertools.product(WE2q, WE1q)]+                                  [2*w2- 2*log(K(q^(-(a0).valuation(q)))) + 1/3*log(K(q^(-(delta2).valuation(q)))) + 1/3*log(K(q^(-(delta1).valuation(q)))) for w2 in WE2q] +
                                 [-2*w1 for w1 in WE1q])))
            Wqprimelist2.append(Wqprime2)

        W1list = list(itertools.product(*Wqprimelist1))
        W2list = list(itertools.product(*Wqprimelist2))
        Omega1 = []
        Omega2 = []
        for i in W1list:
            Omega1.append(sum(list(i)) + 2*hQ1 - 2*lambdapQ1)
        for i in W2list:
            Omega2.append(sum(list(i)) + 2*hQ2 - 2*lambdapQ2)
        Omega1 = list(Set(Omega1))
        Omega2 = list(Set(Omega2))

        print "Omega1 has %s elements" %len(Omega1)
        print "Omega2 has %s elements" %len(Omega2)
        print "Omega1 is", Omega1
        print "Omega2 is", Omega2

    points = []
    for P in D0:
        if P[1] == 0:
            print 'Note: there are some finite Weierstrass disks! Beware of precision!'
        Q = Q_lift(HK, P, p)
        xx, yy = HK.local_coord(Q, prec=n)
        f2plus = X_to_E2map_plus(Q, E2K, a0)
        f2plus = H2K(f2plus[0], f2plus[1])
        x_in_disk_of_f2_plus, y_in_disk_of_f2_plus = param_f2Xplus(xx, yy, E2K, a0)
        f2min = X_to_E2map_minus(Q, E2K, a0)
        f2min = H2K(f2min[0], f2min[1])
        x_in_disk_of_f2_minus, y_in_disk_of_f2_minus = param_f2Xmin(xx, yy, E2K, a0)

        f2 = X_to_E2map(Q, E2K, a0)
        x_in_disk_of_f2, y_in_disk_of_f2 = param_f2(xx, yy, a0)
        f2 = H2K(f2[0], f2[1], f2[2])
        f1 = X_to_E1map(Q, E1K)
        x_in_disk_of_f1, y_in_disk_of_f1 = param_f1(xx, yy)
        f1 = H1K(f1[0], f1[1])

        #Single Coleman integrals series:
        t = x_in_disk_of_f1.parent().gens()[0]
        dx_f1 = x_in_disk_of_f1.derivative()
        const_term_f1 = coleman_integrals_on_basis(H1K, H1K(0, 1, 0), f1, inverse_frob1, forms1)[0]
        log_near_f1 = (dx_f1/(2*y_in_disk_of_f1)).integral() + const_term_f1
        log_near_f1 = log_near_f1(p*t)

        dx_f2 = x_in_disk_of_f2.derivative()
        const_term_f2 = coleman_integrals_on_basis(H2K, H2K(0,1,0), f2, inverse_frob2, forms2)[0]
        log_near_f2 = (dx_f2/(2*y_in_disk_of_f2)).integral() + const_term_f2
        log_near_f2 = log_near_f2(p*t)

        #The power series giving the local heights:
        t = x_in_disk_of_f2_plus.parent().gens()[0]
        x_f2_plus_new = x_in_disk_of_f2_plus(p*t)
        y_f2_plus_new = y_in_disk_of_f2_plus(p*t)
        x_f2_minus_new = x_in_disk_of_f2_minus(p*t)
        y_f2_minus_new = y_in_disk_of_f2_minus(p*t)

        Eloc2min = E2min.change_ring(FractionField(x_f2_plus_new.parent()))
        x_f2_plus_new_Emin = u2^2*x_f2_plus_new + r2
        y_f2_plus_new_Emin = u2^3*y_f2_plus_new + s2*u2^2*x_f2_plus_new + tt2
        x_f2_minus_new_Emin = u2^2*x_f2_minus_new + r2
        y_f2_minus_new_Emin = u2^3*y_f2_minus_new + s2*u2^2*x_f2_minus_new + tt2

        point_around_f2_plus = Eloc2min(x_f2_plus_new_Emin, y_f2_plus_new_Emin)
        point_around_f2_minus = Eloc2min(x_f2_minus_new_Emin, y_f2_minus_new_Emin)
        mf2_plus = m2*point_around_f2_plus
        mf2_minus = m2*point_around_f2_minus
        sigma_nearmf2_plus = sigma2.truncate(n)((-mf2_plus[0]/mf2_plus[1]).power_series())
        sigma_nearmf2_minus = sigma2.truncate(n)((-mf2_minus[0]/mf2_minus[1]).power_series())
        if m2 % 2 != 0:
            fm_nearmf2_plus = fm2(x_f2_plus_new_Emin)
            fm_nearmf2_minus = fm2(x_f2_minus_new_Emin)
        else:
            fm_nearmf2_plus = fm2(x_f2_plus_new_Emin, y_f2_plus_new_Emin)
            fm_nearmf2_minus = fm2(x_f2_minus_new_Emin, y_f2_minus_new_Emin)

        try:
            sigmaoverfm_nearmf2_plus = sigma_nearmf2_plus/fm_nearmf2_plus
            sigmaoverfm_nearmf2_minus = sigma_nearmf2_minus/fm_nearmf2_minus
        except TypeError:
            sigmaoverfm_nearmf2_plus = sigma_nearmf2_plus/fm_nearmf2_plus.power_series()
            sigmaoverfm_nearmf2_minus = sigma_nearmf2_minus/fm_nearmf2_minus.power_series()

        try:
            sigmaoverfm_nearmf2_plus = sigmaoverfm_nearmf2_plus.power_series()
        except AttributeError:
            pass
        try:
            sigmaoverfm_nearmf2_minus = sigmaoverfm_nearmf2_minus.power_series()
        except AttributeError:
            pass

        h_nearf2_plus = -2*((sigmaoverfm_nearmf2_plus/sigmaoverfm_nearmf2_plus[0]).log(prec=n) + sigmaoverfm_nearmf2_plus[0].log())/m2^2
        h_nearf2_minus = -2*((sigmaoverfm_nearmf2_minus/sigmaoverfm_nearmf2_minus[0]).log(prec=n) + sigmaoverfm_nearmf2_minus[0].log())/m2^2

        t = x_in_disk_of_f1.parent().gens()[0]
        x_f1_new = x_in_disk_of_f1(p*t)
        y_f1_new = y_in_disk_of_f1(p*t)

        Eloc1min = E1min.change_ring(FractionField(x_f1_new.parent()))
        x_f1_new_Emin = u1^2*x_f1_new + r1
        y_f1_new_Emin = u1^3*y_f1_new + s1*u1^2*x_f1_new + tt1

        point_around_f1 = Eloc1min(x_f1_new_Emin, y_f1_new_Emin)
        mf1 = m1*point_around_f1
        sigma_nearmf1 = sigma1.truncate(n)((-mf1[0]/mf1[1]).power_series())

        if m1 % 2 != 0:
            fm_nearmf1 = fm1(x_f1_new_Emin)
        else:
            fm_nearmf1 = fm1(x_f1_new_Emin, y_f1_new_Emin)

        sigmaoverfm_nearmf1 = sigma_nearmf1/fm_nearmf1
        h_nearf1 = -2*((sigmaoverfm_nearmf1/sigmaoverfm_nearmf1[0]).log(prec=n) + sigmaoverfm_nearmf1[0].log())/m1^2

        rho2 = 2*h_nearf1 - h_nearf2_plus - h_nearf2_minus - 2*alpha1*(log_near_f1)^2 + 2*alpha2*(log_near_f2^2 + logE2_a0K^2)

        for omega in Omega2:
            rho2omega = rho2 - Qp(p, prec-val_sigma-2)(omega)
            k = min(rho2omega[i].valuation(p) for i in range(rho2omega.precision_absolute()))
            M = min(rho2omega.precision_absolute()-3, prec-val_sigma-3)
            nprime = M#-3
            ndoubleprime = nprime-k#-5
            while rho2omega[nprime-1] == 0:
                nprime += -1
            ndoubleprime = nprime-k#-5

            if bernardi == False:
                rho2omega_val = rho2omega.valuation()
                if rho2omega_val > 0:
                    roots = [0]
                else:
                    roots = []
                roots.extend(list(gp.polrootspadic((rho2omega/(rho2omega.parent().0^rho2omega_val*p^k)).truncate(nprime - rho2omega_val), p, 1)))
            else:
                rho2omega = rho2omega + (1+O(p^nprime)) - 1
                rho2omega_val = rho2omega.valuation()
                if rho2omega_val > 0:
                    roots = [0]
                else:
                    roots = []
                roots.extend(list(gp.polrootspadic((rho2omega/(rho2omega.parent().0^rho2omega_val*p^k)).truncate(nprime - rho2omega_val), p, 1)))

            roots = [p*r + O(p^ndoubleprime) for r in roots if r.valuation(p) >= 0]
            new_points = [HK(xx(K(sage_eval('%s'%t0))), yy(K(sage_eval('%s'%t0)))) for t0 in roots]
            points.extend(new_points)

    for P in D:
        if P[1] == 0:
            print 'Note: there are some finite Weierstrass disks! Beware of precision!'
        if P[2] != 0:
            Q = Q_lift(HK, P, p)
            xx, yy = HK.local_coord(Q, prec = n)
        else:
            Q = HK(0, 1, 0)
            xx, yy = local_coordinates_at_infinity_new(HK, prec = n)
            t = xx.parent().gens()[0]

        f1plus = X_to_E1map_plus(Q, E1K, a0)
        f1plus = H1K(f1plus[0], f1plus[1])
        x_in_disk_of_f1_plus, y_in_disk_of_f1_plus = param_f1Xplus(xx, yy, E1K, p, prec, a0)

        f1minus = X_to_E1map_minus(Q, E1K, a0)
        f1minus = H1K(f1minus[0], f1minus[1])
        x_in_disk_of_f1_minus, y_in_disk_of_f1_minus = param_f1Xmin(xx, yy, E1K, p, prec, a0)

        f2 = X_to_E2map(Q, E2K, a0)
        f2 = H2K(f2[0], f2[1])
        x_in_disk_of_f2, y_in_disk_of_f2 = param_f2(xx, yy, a0)

        if Q != HK(0, 1, 0):
            f1 = X_to_E1map(Q, E1K)
            x_in_disk_of_f1, y_in_disk_of_f1 = param_f1(xx, yy)
            f1 = H1K(f1[0], f1[1])

            #Single Coleman integral series:
            t = x_in_disk_of_f1.parent().gens()[0]
            dx_f1 = x_in_disk_of_f1.derivative()
            const_term_f1 = coleman_integrals_on_basis(H1K, H1K(0, 1, 0), f1, inverse_frob1, forms1)[0]
            log_near_f1 = (dx_f1/(2*y_in_disk_of_f1)).integral() + const_term_f1
            log_near_f1 = log_near_f1(p*t)
        else:
            xf1z = xx^2
            yf1z = yy
            log_near_f1 = (xf1z.derivative()/(2*yf1z)).integral().power_series()
            log_near_f1 = log_near_f1(p*t)

        dx_f2 = x_in_disk_of_f2.derivative()
        const_term_f2 = coleman_integrals_on_basis(H2K, H2K(0, 1, 0), f2, inverse_frob2, forms2)[0]
        log_near_f2 = (dx_f2/(2*y_in_disk_of_f2)).integral() + const_term_f2
        log_near_f2 = log_near_f2(p*t)

        #The power series giving the local heights:
        t = x_in_disk_of_f1_plus.parent().gens()[0]
        x_f1_plus_new = x_in_disk_of_f1_plus(p*t)
        y_f1_plus_new = y_in_disk_of_f1_plus(p*t)
        x_f1_minus_new = x_in_disk_of_f1_minus(p*t)
        y_f1_minus_new = y_in_disk_of_f1_minus(p*t)

        Eloc1min = E1min.change_ring(FractionField(x_f1_plus_new.parent()))
        x_f1_plus_new_Emin = u1^2*x_f1_plus_new + r1
        y_f1_plus_new_Emin = u1^3*y_f1_plus_new + s1*u1^2*x_f1_plus_new + tt1
        x_f1_minus_new_Emin = u1^2*x_f1_minus_new + r1
        y_f1_minus_new_Emin = u1^3*y_f1_minus_new + s1*u1^2*x_f1_minus_new + tt1

        point_around_f1_plus = Eloc1min(x_f1_plus_new_Emin, y_f1_plus_new_Emin)
        point_around_f1_minus = Eloc1min(x_f1_minus_new_Emin, y_f1_minus_new_Emin)
        mf1_plus = m1*point_around_f1_plus
        mf1_minus = m1*point_around_f1_minus
        sigma_nearmf1_plus = sigma1.truncate(n)((-mf1_plus[0]/mf1_plus[1]).power_series())
        sigma_nearmf1_minus = sigma1.truncate(n)((-mf1_minus[0]/mf1_minus[1]).power_series())
        if m1 % 2 != 0:
            fm_nearmf1_plus = fm1(x_f1_plus_new_Emin)
            fm_nearmf1_minus = fm1(x_f1_minus_new_Emin)
        else:
            fm_nearmf1_plus = fm1(x_f1_plus_new_Emin, y_f1_plus_new_Emin)
            fm_nearmf1_minus = fm1(x_f1_minus_new_Emin, y_f1_minus_new_Emin)

        if Q == HK(0,1,0):
            fm_nearmf1_plus = fm_nearmf1_plus.power_series()
            fm_nearmf1_minus = fm_nearmf1_minus.power_series()
        sigmaoverfm_nearmf1_plus = sigma_nearmf1_plus/fm_nearmf1_plus
        sigmaoverfm_nearmf1_minus = sigma_nearmf1_minus/fm_nearmf1_minus

        h_nearf1_plus = -2*((sigmaoverfm_nearmf1_plus/sigmaoverfm_nearmf1_plus[0]).log(prec=n) + sigmaoverfm_nearmf1_plus[0].log())/m1^2
        h_nearf1_minus = -2*((sigmaoverfm_nearmf1_minus/sigmaoverfm_nearmf1_minus[0]).log(prec=n) + sigmaoverfm_nearmf1_minus[0].log())/m1^2

        t = x_in_disk_of_f2.parent().gens()[0]
        x_f2_new = x_in_disk_of_f2(p*t)
        y_f2_new = y_in_disk_of_f2(p*t)

        Eloc2min = E2min.change_ring(FractionField(x_f2_new.parent()))
        x_f2_new_Emin = u2^2*x_f2_new + r2
        y_f2_new_Emin = u2^3*y_f2_new + s2*u2^2*x_f2_new + tt2

        point_around_f2 = Eloc2min(x_f2_new_Emin,y_f2_new_Emin)
        mf2 = m2*point_around_f2
        sigma_nearmf2 = sigma2.truncate(n)((-mf2[0]/mf2[1]).power_series())

        if m2 % 2 != 0:
            fm_nearmf2 = fm2(x_f2_new_Emin)
        else:
            fm_nearmf2 = fm2(x_f2_new_Emin, y_f2_new_Emin)
        if Q == HK(0,1,0):
            fm_nearmf2 = fm_nearmf2.power_series()
        sigmaoverfm_nearmf2 = sigma_nearmf2/fm_nearmf2
        h_nearf2 = -2*((sigmaoverfm_nearmf2/sigmaoverfm_nearmf2[0]).log(prec=n)+sigmaoverfm_nearmf2[0].log())/m2^2
        if Q == HK(0, 1, 0):
            rho1 = 2*h_nearf2 - h_nearf1_plus - h_nearf1_minus - 2*alpha2*(log_near_f2^2).power_series() + 2*alpha1*((log_near_f1^2).power_series()) + 2*hQ1
        else:
            rho1 = 2*h_nearf2 - h_nearf1_plus - h_nearf1_minus - 2*alpha2*(log_near_f2)^2 + 2*alpha1*(log_near_f1^2) + 2*hQ1

        for omega in Omega1:
            rho1omega = rho1 - Qp(p,prec-val_sigma-2)(omega)
            k = min(rho1omega[i].valuation(p) for i in range(rho1omega.precision_absolute()))
            M = min(rho1omega.precision_absolute()-3,prec-val_sigma-3)
            nprime = M#-3
            ndoubleprime = nprime-k#-5
            while rho1omega[nprime-1] == 0 or rho1omega[nprime-1].valuation(p)<0:
                nprime += -1
            ndoubleprime = nprime-k#-5

            if bernardi == False:
                rho1omega_val = rho1omega.valuation()
                if rho1omega_val > 0:
                    roots = [0]
                else:
                    roots = []
                roots.extend(list(gp.polrootspadic((rho1omega/(rho1omega.parent().0^rho1omega_val*p^k)).truncate(nprime - rho1omega_val), p, 1)))
            else:
                rho1omega = rho1omega + (1+O(p^nprime))-1
                rho1omega_val = rho1omega.valuation()
                if rho1omega_val > 0:
                    roots = [0]
                else:
                    roots = []
                roots.extend(list(gp.polrootspadic((rho1omega/(rho1omega.parent().0^rho1omega_val*p^k)).truncate(nprime - rho1omega_val), p, 1)))

            roots = [p*r + O(p^ndoubleprime) for r in roots if r.valuation(p) >= 0]
            if Q != HK(0, 1, 0):
                new_points = [HK(xx(K(sage_eval('%s'%t0))), yy(K(sage_eval('%s'%t0)))) for t0 in roots]
                points.extend(new_points)
            else:
                if rho1omega[0] == 0:
                    points.append(H(0, 1, 0))
                new_points = [HK(xx(K(sage_eval('%s'%t0))), yy(K(sage_eval('%s'%t0)))) for t0 in roots if t0 != 0]
                points.extend(new_points)

    rational_points = []
    other_points = []
    for P in points:
        if P == H(0, 1, 0):
            rational_points.append(H(0, 1, 0))
            continue
        try:
            RP = H.lift_x(QQ(P[0]))
            if RP[1] - P[1] == 0:
                rational_points.append(RP)
            else:
                RP = H(RP[0], -RP[1])
                rational_points.append(RP)
        except ValueError:
            pol = algdep(P[0], 1)
            pol = PolynomialRing(QQ, "x")(pol)
            try:
                RP = H.lift_x(pol.roots()[0][0])
                if RP[1] - P[1] == 0:
                    rational_points.append(RP)
                else:
                    RP = H(RP[0], -RP[1])
                    rational_points.append(RP)
            except ValueError:
                    other_points.append(P)
    rational_points.sort()
    other_points.sort()
    return rational_points, other_points
