r"""
Quadratic Chabauty for elliptic curves over `\QQ` of rank at most `1`.

Code for the elliptic curves computations of [Bia19].
The main functions are `quadratic_chabauty_rank_0` and
`quadratic_chabauty_rank_1`. See their respective
docstrings for details on input and output and for more
examples.

REFERENCES:

- [Bia19] \F. Bianchi, "Quadratic Chabauty for (bi)elliptic curves
  and Kim's conjecture".


EXAMPLES::

An example in rank `0` ([Bia19, Example 4.4])::

    sage: E = EllipticCurve("11025.y2"); p = 13; prec = 20
    sage: int_points, number_extra_points, extra_points = quadratic_chabauty_rank_0(E, p, prec)
    sage: int_points
    [(0 : 122 : 1)]
    sage: if number_extra_points != 0:
    ....:     for P in extra_points:
    ....:         try:
    ....:             algdep(P[0],3)
    ....:         except PariError:
    ....:             print P
    x^3 - 120050
    x^3 - 120050
    x^3 - 120050


Changing the prime::

    sage: int_points, number_extra_points, extra_points = quadratic_chabauty_rank_0(E, 31, 20)
    sage: int_points
    [(0 : -123 : 1)]
    sage: number_extra_points
    0

An example in rank `1` ([Bia19, Example 5.4])::

    sage: E = EllipticCurve("576.e4")
    sage: E.rank()
    1
    sage: int_points, number_extra_points, extra_points = quadratic_chabauty_rank_1(E, 7, 20, torsion=True)
    sage: int_points
    [[(-2 : 0 : 1)], [(1 : 3 : 1), (2 : -4 : 1), (46 : -312 : 1)]]
    sage: number_extra_points
    [2, 17]
    sage: extra_points[0]
    [(x^2 - 2*x + 4, 0), (x^2 - 2*x + 4, 0)]
    sage: for P in extra_points[1]:
    ....:     if type(P) == tuple:
    ....:         print P
    (x^2 + 10*x + 28, x^2 - 12*x + 144)
    (x^2 + 10*x + 28, x^2 + 12*x + 144)

Note that::

    sage: int_points_0, number_extra_points_0, extra_points_0 = quadratic_chabauty_rank_0(E, 7, 20)
    sage: int_points_0 == int_points[0]
    True
    sage: number_extra_points_0 == number_extra_points[0]
    True
    sage: extra_points_0 == extra_points[0]
    True

AUTHORS:

- FRANCESCA BIANCHI (started: April 2018; this version: March 2019)


"""

############## AUXILIARY FUNCTIONS ##############

import itertools
import sage.schemes.hyperelliptic_curves.monsky_washnitzer as monsky_washnitzer


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

    - ``p`` -- the prime of the first two inputs.

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


def integral_points_rank_0(E, both_signs=False):
    r"""
    Compute the torsion integral points on an elliptic curve.

    INPUT:

    - ``E`` -- an elliptic curve over a number field.

    - ``both_signs`` -- True/False (default False): if True the
      output contains both P and -P, otherwise only one of each pair.

    OUTPUT: A sorted list of all the integral points on E (up to sign
    unless both_signs is True).

    """
    tors_points = E.torsion_points()
    int_points = [P for P in tors_points if not P.is_zero()]
    int_points = [P for P in int_points if P[0].is_integral()]
    if not both_signs:
        xlist = set([P[0] for P in int_points])
        int_points = [E.lift_x(x) for x in xlist]
    int_points.sort()
    return int_points


def local_heights_at_bad_primes(E, K):
    r"""
    Compute all possible sums of local heights at bad places for an integral point.

    INPUT:

    - ``E`` -- an elliptic curve over `\QQ`. `E` should be given by a
      minimal Weierstrass equation.

    - ``K`` -- `\QQ_p` for some `p` at which `E` has good reduction.

    OUTPUT: A list of all possible values of the sum of the `p`-adic local heights
    away from `p` for an integral point on `E`.
    """
    bad_primes = E.base_ring()(E.integral_model().discriminant()).support()
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

    W = list(itertools.product(*W))
    possible_sums = []
    for i in W:
        possible_sums.append(sum(list(i)))

    return possible_sums


def bernardi_sigma_function(E, prec=20):
    r"""
     Return the sigma function of Bernardi in terms of `z = log(t)`.
    This is an adaptation of the code built in sage. The difference is that we input
    the curve istead of the `L`-function and that we are adding `r` to `xofF`.

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


def sorting_fct(P):
    r"""
    Return `0` if input is a tuple, `1` otherwise.
    """
    if type(P) == tuple:
        return 0
    else:
        return 1


############## MAIN FUNCTIONS ###############


def quadratic_chabauty_rank_0(E, p, n, bernardi=False):
    r"""
    Do quadratic Chabauty on a rank `0` elliptic curve.

    INPUT:

    - ``E`` -- an elliptic curve over `\QQ`. If `E` has non-trivial
      rank, then the obvious analogues will be computed.

    - ``p`` -- an odd prime of good reduction for `E.`

    - ``n`` -- working `p`-adic precision.

    - ``bernardi`` -- True/False (default False): if False and `p`
      is ordinary and `\ge 5`, the Mazur-Tate sigma function is used;
      otherwise, the Bernardi one.

    OUTPUT: A tuple consisting of

    - A sorted list of all the integral points on `E`, up to sign.
      (Warning: if the precision is low, it could happen that an integral
      point is not recognised. In that case, it will appear in the third item of
      the tuple and will be counted in the second one.)

    - The size of `X(\ZZ_p)_2/<\pm 1> \setminus X(\ZZ)/<\pm 1>`.

    - The list of points in `X(\ZZ_p)^{\prime}_2/<\pm 1> \setminus X(\ZZ)/<\pm 1>`.
      If a point is recognised as algebraic, it is represented as a tuple of
      minimal polynomials/rational numbers. The list is sorted so that the recognised
      algebraic points appear first.
      If `X(\ZZ_p)_2` is trivial because either `E` has good reduction at `q \in \{2,3\}`
      and `E(GF(q))` has size `1` or `E` has split multiplicative reduction at `2` with
      Tamagawa number `1`, then ``trival`` is returned as the third output.


    EXAMPLES::

        sage: E = EllipticCurve("14440.g4")
        sage: quadratic_chabauty_rank_0(E,7,30)
        ([(-38 : 0 : 1)], 1, [(-133, x^2 + 2743600)])

    A trivial example ([Bia19, Example 4.2])::

        sage: E = EllipticCurve("121.d3")
        sage: quadratic_chabauty_rank_0(E, 5, 20)
        ([], 0, 'trivial')
        sage: E.Np(2)
        1
    """

    #Trivial cases:
    if E.has_good_reduction(2) == True:
        if E.Np(2) == 1:
            return [], 0, "trivial"

    if E.has_good_reduction(3) == True:
        if E.Np(3) == 1:
            return [], 0, "trivial"

    if E.has_split_multiplicative_reduction(2) == True:
        if E.kodaira_symbol(2) == KodairaSymbol(5):
            return [], 0, "trivial"

    #Non-trivial cases:
    K = Qp(p, n)
    Zpn = Zp(p, prec = n)
    _.<x> = PolynomialRing(Rationals())
    Eshort = E.short_weierstrass_model()
    phi = Eshort.isomorphism_to(E)
    psi = E.isomorphism_to(Eshort)
    a4 = Eshort.a4()
    a6 = Eshort.a6()
    [u, r, s, tt] = psi.tuple()
    H = HyperellipticCurve(x^3 + a4*x + a6)
    HK = H.change_ring(K)
    HZpn = H.change_ring(Zpn)
    Hp = H.change_ring(GF(p))
    SK = K[['t']]
    t = SK.gen()
    SK.set_default_prec(n+2)

    #Compute Frobenius data only once:
    M_frob, forms = monsky_washnitzer.matrix_of_frobenius_hyperelliptic(HK)
    forms = [form.change_ring(K) for form in forms]
    M_sys = matrix(K, M_frob).transpose() - 1
    inverse_frob = M_sys**(-1)

    if E.is_ordinary(p) and bernardi == False:
        sigma = E.padic_sigma(p, n)
    else:
        sigma = bernardi_sigma_function(E, prec=n)
        sigma = sigma(E.formal().log(n))
        val_sigma = max(sigma[i].denominator().valuation(p) for i in range(sigma.precision_absolute()))

    classes_to_consider = [Q for Q in list(Hp.points()) if ZZ(Q[1]) < p/2]
    order_points_1 = []
    for Q in classes_to_consider:
        mQ = Eshort.change_ring(GF(p))(Q).order()
        order_points_1.append(mQ)
    order_points = list(Set(order_points_1))

    order_div_poly = [0 for i in range(len(order_points_1))]
    for mQ in order_points:
        if mQ % 2 != 0:
            fmQ = E.division_polynomial(mQ)
        else:
            fmQ = E.division_polynomial(mQ, two_torsion_multiplicity=1)
        for i in range(len(order_points_1)):
            if order_points_1[i] == mQ:
                order_div_poly[i] = fmQ
    number_Fp_points = len(Hp.points())

    W = local_heights_at_bad_primes(E, K)

    all_integral_points = []
    count_extra_points = 0
    points_new_all_classes = []

    for Q in classes_to_consider:
        if Q == Hp(0, 1, 0):
            continue
        indexQ = classes_to_consider.index(Q)
        m = order_points_1[indexQ]
        fm = order_div_poly[indexQ]
        R = Q_lift(HK, Q, p)
        RZpn = HZpn(R)
        xR, yR =  HZpn.local_coord(RZpn, prec=n+2)
        xR = SK(xR)
        yR = SK(yR)
        dx = xR.derivative()
        const_term = coleman_integrals_on_basis(HK, HK(0, 1, 0), R, inverse_frob, forms)[0]
        log_near_R = (dx/(2*yR)).integral() + const_term
        log_near_R = log_near_R(p*t)
        xRnew = xR(p*t)
        yRnew = yR(p*t)
        Eloc = E.change_ring(FractionField(xR.parent()))
        xRE = u^2*xRnew + r
        yRE = u^3*yRnew + s*u^2*xRnew + tt
        point_around_R = Eloc(xRE,yRE)
        mxRyR = m*point_around_R
        sigma_near_mR = sigma.truncate(n)((-mxRyR[0]/mxRyR[1]).power_series())
        if m % 2 != 0:
            fm_near_R = fm(xRE)
        else:
            fm_near_R = fm(xRE, yRE)
        sigma_over_fm = sigma_near_mR/fm_near_R
        lambda_p_near_R = -2*((sigma_over_fm/sigma_over_fm[0]).log(prec=n) + sigma_over_fm[0].log())/m^2 #Note that if the reduction is supersingular the coefficients of the series will be correct only up to the given absolute precision - val_sigma. This is taken care of in the roots but not here,
        #that is some digits of h could be wrong
        hW = [lambda_p_near_R + w for w in W]

        k = min((log_near_R[0]).valuation(), 1) #minimal valuation of the coefficients of log_near_R
        if number_Fp_points % p == 0:
            k = k + 2
        M = n
        Mprime = n
        while Mprime % p != 0:
                Mprime += 1
        if Mprime - Mprime.valuation(p) < n:
            M = Mprime + 1
        ndoubleprime = M-k

        if const_term == 0:
            roots_log = [Qp(p, n)(0)]
            tR = log_near_R.parent().gens()[0]
            roots_log.extend(list(gp.polrootspadic((log_near_R/tR).truncate(M-1), p, 1)))
        else:
            roots_log = list(gp.polrootspadic((log_near_R).truncate(M), p, 1))
        roots_log = [p*x + O(p^ndoubleprime) for x in roots_log if x.valuation(p) >= 0]
        if number_Fp_points % p != 0:
            assert len(roots_log) == 1, "Not the right number of roots found for the logarithm for Q = %" %Q
        else:
            assert len(roots_log) <= 1, "Not the right number of roots found for the logarithm for Q = %" %Q

        #Note in particular that the roots of the logarithm are simple

        if roots_log == []:
            continue
        integral_points_class = []
        points_new_class = []
        count_extra_points_class = 0

        for h in hW:
            commonroots = []
            if E.is_ordinary(p) == True and bernardi == False:
                for t0 in roots_log:
                    if h.truncate()(K(sage_eval('%s'%t0))/p) == 0:
                        commonroots.append(t0)
            else:
                for t0 in roots_log:
                    h_value = h.truncate()(K(sage_eval('%s'%t0))/p)
                    if h_value.valuation() >= (h_value.precision_absolute() - val_sigma):#I may need to be more careful with precision in supersingular case!
                        commonroots.append(t0)

            points = [HK(xR(K(sage_eval('%s'%t0))), yR(K(sage_eval('%s'%t0)))) for t0 in commonroots]
            integral_points = []
            points_new = []

            points = [E.change_ring(K)(u^2*Q[0]+r, u^3*Q[1]+s*u^2*Q[0]+tt) for Q in points]
            for A in points:
                try:
                    NIP = E.lift_x(QQ(A[0]))
                    if NIP[1] - A[1] == 0:
                        integral_points.append(NIP)
                    else:
                        NIP = -E(NIP[0], NIP[1])
                        integral_points.append(NIP)
                except ValueError:
                    points_new.append(A)

            if points_new != []:
                #print "The contribution at bad primes is %s" %(W[hW.index(h)])
                for A in points_new:
                    i = points_new.index(A)
                    p1 = algdep(A[0],2)
                    p2 = algdep(A[1],2)
                    if p1.is_irreducible() and p2.is_irreducible():
                        Lf.<par> = NumberField(p2)
                        if p1.degree() == 1:
                            try:
                                OTP = E.change_ring(Lf).lift_x(QQ(A[0]))
                                if p2(OTP[1]) == 0 or p2((-OTP)[1]) == 0:
                                    points_new[i] = (QQ(A[0]),p2)
                            except ValueError:
                                pass
                        else:
                            Lf.<par> = NumberField(p1)
                            try:
                                OTP = E.change_ring(Lf).lift_x(par)
                                if p2(OTP[1]) == 0 or p2((-OTP)[1]) == 0:
                                    if p2.degree() == 1:
                                        points_new[i] = (p1,QQ(A[1]))
                                    else:
                                        points_new[i] = (p1,p2)
                                else:
                                    continue
                            except ValueError:
                                continue
            integral_points_class.extend(integral_points)
            points_new_class.extend(points_new)
            count_extra_points_class += len(points_new)
            if len(integral_points_class) + count_extra_points_class == len(roots_log):
                break
        all_integral_points.extend(integral_points_class)
        points_new_all_classes.extend(points_new_class)
        count_extra_points += count_extra_points_class
    all_integral_points.sort()
    points_new_all_classes.sort(key=sorting_fct)
    return all_integral_points, count_extra_points, points_new_all_classes


def quadratic_chabauty_rank_1(E, p, n, torsion=False, Pshort=None):
    r"""
    Do quadratic Chabauty on a rank 1 elliptic curve.

    INPUT:

    - ``E`` -- an elliptic curve over `\QQ` of rank `1`.

    - ``p`` -- an odd prime `\ge 5` of good ordinary reduction for E.

    - ``n`` -- working p-adic precision.

    - ``torsion`` --  True/False (default False): if True, each output
      item is split in torsion and non-torsion points.

    - ``Pshort`` (optional) -- a point of infinite order on the short
      Weierstrass model obtained from E via `E.short_weierstrass_model()`.

    OUTPUT:

    A tuple consisting of:

    - A sorted list of all the integral points on E, up to sign.
      (Warning: if the precision is low, it could happen that an integral
      point is not recognised. In that case, it will appear in the third item of
      the tuple and will be counted in the second one.)

    - The size of `X({\ZZ}_p)^{\prime}_2/<\pm 1> \setminus X(\ZZ)/<\pm 1>`.

    - The list of points in `X(\ZZ_p)^{\prime}_2/<\pm 1> \setminus X(\ZZ)/<\pm 1>`.
      If a point is recognised as algebraic, it is represented as a tuple of
      minimal polynomials/rational numbers. The list is sorted so that the recognised
      algebraic points appear first.
      If `X(\ZZ_p)_2` is trivial because either `E` has good reduction at `q \in \{2,3\}`
      and `E(GF(q))` has size `1` or `E` has split multiplicative reduction at `2` with
      Tamagawa number `1`, then ``trival`` is returned as the third output.

    .. NOTE:: If `E` has larger rank and `Pshort` is provided, then the obvious analogue
        of `X({\ZZ}_p)^{\prime}_2/<\pm 1>` is returned.

    .. TO DO:: Add supersingular case.

    EXAMPLES::

    An example of `X(\ZZ_p)^{\prime}_2 = X(\ZZ)`::

        sage: E = EllipticCurve("297.b1")
        sage: quadratic_chabauty_rank_1(E, 5, 25)
        ([(0 : -1 : 1), (3 : 3 : 1)], 0, [])

    An example where SageMath version 8.6 can't find all integral points
    (see also https://github.com/LMFDB/lmfdb/issues/2600 )::

        sage: E = EllipticCurve("2082.a1")
        sage: int_points, number_extra_points, extra_points = quadratic_chabauty_rank_1(E, 5, 40)
        sage: int_points
        [(-11 : -19 : 1),
         (-2 : 29 : 1),
         (4 : 11 : 1),
         (13 : 29 : 1),
         (507525709 : 11433453531221 : 1)]
        sage: E.integral_points()
        [(-11 : 29 : 1), (-2 : 29 : 1), (4 : 11 : 1), (13 : 29 : 1)]

    """
    #Trivial cases:
    if E.has_good_reduction(2) == True:
        if E.Np(2) == 1:
            return [], 0, "trivial"

    if E.has_good_reduction(3) == True:
        if E.Np(3) == 1:
            return [], 0, "trivial"

    if E.has_split_multiplicative_reduction(2) == True:
        if E.kodaira_symbol(2) == KodairaSymbol(5):
            return [], 0, "trivial"

    #Non-trivial cases:
    K = Qp(p, n)
    Zpn = Zp(p, prec = n)
    _.<x> = PolynomialRing(Rationals())
    Eshort = E.short_weierstrass_model()
    phi = Eshort.isomorphism_to(E)
    psi = E.isomorphism_to(Eshort)
    a4 = Eshort.a4()
    a6 = Eshort.a6()
    [u, r, s, tt] = psi.tuple()
    H = HyperellipticCurve(x^3 + a4*x + a6)
    HK = H.change_ring(K)
    HZpn = H.change_ring(Zpn)
    Hp = H.change_ring(GF(p))
    SK = K[['t']]
    t = SK.gen()
    SK.set_default_prec(n+2)

    #Compute Frobenius data only once:
    M_frob, forms = monsky_washnitzer.matrix_of_frobenius_hyperelliptic(HK)
    forms = [form.change_ring(K) for form in forms]
    M_sys = matrix(K, M_frob).transpose() - 1
    inverse_frob = M_sys**(-1)

    sigma = E.padic_sigma(p,n)

    if Pshort == None:
        Pshort = Eshort.gens()[0]
    P = phi(Pshort)
    PH = H(Pshort[0], Pshort[1])
    if PH[0].valuation(p) < 0:
        log_P =  HK.tiny_integrals([1], HK(0,1,0), HK(PH))[0] #tiny_integrals gives the right answer in the disk at infty, but only up to O(p^20) in other disks
    elif PH[1] % p != 0:
        log_P = coleman_integrals_on_basis(HK, HK(0,1,0), HK(PH), inverse_frob, forms)[0]
    else:
        PHp = Hp(PH)
        Wlift = Q_lift(HK, PHp, p)
        x_Wlift, y_Wlift =  HK.local_coord(Wlift, prec=n+2)
        dx_Wlift = x_Wlift.derivative()
        log_near_Wlift = (dx_Wlift/(2*y_Wlift)).integral()
        log_P = log_near_Wlift.truncate()(PH[1])

    h = E.padic_height(p, n)
    hP = h(P)

    classes_to_consider = [Q for Q in list(Hp.points()) if ZZ(Q[1]) < p/2]
    order_points_1 = []
    for Q in classes_to_consider:
        mQ = Eshort.change_ring(GF(p))(Q).order()
        order_points_1.append(mQ)
    order_points = list(Set(order_points_1))

    order_div_poly = [0 for i in range(len(order_points_1))]
    for mQ in order_points:
        if mQ % 2 != 0:
            fmQ = E.division_polynomial(mQ)
        else:
            fmQ = E.division_polynomial(mQ, two_torsion_multiplicity=1)
        for i in range(len(order_points_1)):
            if order_points_1[i] == mQ:
                order_div_poly[i] = fmQ
    number_Fp_points = len(Hp.points())

    W = local_heights_at_bad_primes(E, K)

    if torsion == False:
        points_new_all_classes = []
        all_integral_points = []
        count_extra_points = 0
    else:
        points_new_torsion_all_classes = []
        all_integral_points_torsion = []
        count_extra_points_torsion = 0
        points_new_non_torsion_all_classes = []
        all_integral_points_non_torsion = []
        count_extra_points_non_torsion = 0

    for Q in classes_to_consider:
        if Q == Hp(0, 1, 0):
            continue
        indexQ = classes_to_consider.index(Q)
        m = order_points_1[indexQ]
        fm = order_div_poly[indexQ]
        R = Q_lift(HK, Q, p)
        RZpn = HZpn(R)
        xR, yR =  HZpn.local_coord(RZpn, prec=n+2)
        xR = SK(xR)
        yR = SK(yR)
        dx = xR.derivative()
        const_term = coleman_integrals_on_basis(HK, HK(0,1,0), R, inverse_frob, forms)[0]
        log_near_R = (dx/(2*yR)).integral() + const_term
        log_near_R_nop = log_near_R
        log_near_R = log_near_R(p*t)
        xRnew = xR(p*t)
        yRnew = yR(p*t)
        Eloc = E.change_ring(FractionField(xR.parent()))
        xRE = u^2*xRnew + r
        yRE = u^3*yRnew + s*u^2*xRnew + tt
        point_around_R = Eloc(xRE, yRE)
        mxRyR = m*point_around_R
        sigma_near_mR = sigma.truncate(n)((-mxRyR[0]/mxRyR[1]).power_series())

        if m % 2 !=0:
            fm_near_R = fm(xRE)
        else:
            fm_near_R = fm(xRE, yRE)
        sigma_over_fm = sigma_near_mR/fm_near_R
        lambda_p_near_R = -2*((sigma_over_fm/sigma_over_fm[0]).log(prec=n) + sigma_over_fm[0].log())/m^2


        hW = [lambda_p_near_R + w for w in W]
        fW = [log_P^2*hw - hP*log_near_R^2 for hw in hW]

        for f in fW:
            M = f.precision_absolute()
            k = min(f[i].valuation(p) for i in range(M))
            nprime = M-3
            while f[nprime-1] == 0:
                nprime += -1
            ndoubleprime = nprime-k-5
            const_term = f[0]

            if const_term == 0:
                roots = [Qp(p, n)(0)]
                tR = f.parent().gens()[0]
                tval = f.valuation()
                roots.extend(list(gp.polrootspadic((f/tR^tval).truncate(nprime-tval)/p^k, p, 1)))
            else:
                roots = list(gp.polrootspadic(f.truncate(nprime)/p^k, p, 1))
            roots = [p*x + O(p^ndoubleprime) for x in roots if x.valuation(p) >= 0]

            if torsion == False:
                if Q[1] != 0:
                    points = [HK(xR(K(sage_eval('%s'%t0))), yR(K(sage_eval('%s'%t0)))) for t0 in roots]
                else:
                    points_with_repetition = [HK(xR(K(sage_eval('%s'%t0))), yR(K(sage_eval('%s'%t0)))) for t0 in roots]
                    x_points = list(Set([pt[0] for pt in points_with_repetition]))
                    points = []
                    for xt0 in x_points:
                        for pt in points_with_repetition:
                            if pt[0] == xt0:
                                points_with_repetition.remove(pt)
                                points.append(pt)
                                break
                points = [E.change_ring(K)(u^2*QP[0] + r, u^3*QP[1] + s*u^2*QP[0] + tt) for QP in points]
                integral_points = []
                points_new = []
                for A in points:
                    try:
                        NIP = E.lift_x(QQ(A[0]))
                        if NIP[1] - A[1] == 0:
                            integral_points.append(NIP)
                        else:
                            NIP = -E(NIP[0],NIP[1])
                            integral_points.append(NIP)
                    except ValueError:
                        points_new.append(A)
                if points_new != []:
                    for A in points_new:
                        i = points_new.index(A)
                        p1 = algdep(A[0],2)
                        p2 = algdep(A[1],2)
                        if p1.is_irreducible() and p2.is_irreducible():
                            Lf.<par> = NumberField(p2)
                            if p1.degree() == 1:
                                try:
                                    OTP = E.change_ring(Lf).lift_x(QQ(A[0]))
                                    if p2(OTP[1]) == 0 or p2((-OTP)[1]) == 0:
                                        points_new[i] = (QQ(A[0]), p2)
                                except ValueError:
                                    pass
                            else:
                                Lf.<par> = NumberField(p1)
                                try:
                                    OTP = E.change_ring(Lf).lift_x(par)
                                    if p2(OTP[1]) == 0 or p2((-OTP)[1]) == 0:
                                        if p2.degree() == 1:
                                            points_new[i] = (p1, QQ(A[1]))
                                        else:
                                            points_new[i] = (p1, p2)
                                    else:
                                        continue
                                except ValueError:
                                    continue

                points_new_all_classes.extend(points_new)
                all_integral_points.extend(integral_points)
                count_extra_points += len(points_new)

            else:
                roots_torsion = [x for x in roots if log_near_R_nop(K(sage_eval('%s'%x))) == 0]
                roots_non_torsion = [x for x in roots if x not in roots_torsion]
                points_torsion = [HK(xR(K(sage_eval('%s'%t0))),yR(K(sage_eval('%s'%t0)))) for t0 in roots_torsion]
                if Q[1] != 0:
                    points_non_torsion = [HK(xR(K(sage_eval('%s'%t0))),yR(K(sage_eval('%s'%t0)))) for t0 in roots_non_torsion]
                else:
                    points_with_repetition_non_torsion = [HK(xR(K(sage_eval('%s'%t0))), yR(K(sage_eval('%s'%t0)))) for t0 in roots_non_torsion]
                    x_points_non_torsion = list(Set([pt[0] for pt in points_with_repetition_non_torsion]))
                    points_non_torsion = []
                    for xt0 in x_points_non_torsion:
                        for pt in points_with_repetition_non_torsion:
                            if pt[0] == xt0:
                                points_with_repetition_non_torsion.remove(pt)
                                points_non_torsion.append(pt)
                                break

                integral_points_torsion = []
                points_new_torsion = []
                points_torsion = [E.change_ring(K)(u^2*QP[0]+r,u^3*QP[1]+s*u^2*QP[0]+tt) for QP in points_torsion]
                for A in points_torsion:
                    try:
                        NIP = E.lift_x(QQ(A[0]))
                        if NIP[1] - A[1] == 0:
                            integral_points_torsion.append(NIP)
                        else:
                            NIP = -E(NIP[0],NIP[1])
                            integral_points_torsion.append(NIP)
                    except ValueError:
                        points_new_torsion.append(A)

                if points_new_torsion != []:
                    for A in points_new_torsion:
                        i = points_new_torsion.index(A)
                        p1 = algdep(A[0],2)
                        p2 = algdep(A[1],2)
                        if p1.is_irreducible() and p2.is_irreducible():
                            Lf.<par> = NumberField(p2)
                            if p1.degree() == 1:
                                try:
                                    OTP = E.change_ring(Lf).lift_x(QQ(A[0]))
                                    if p2(OTP[1]) == 0 or p2((-OTP)[1]) == 0:
                                        points_new_torsion[i] = (QQ(A[0]), p2)
                                except ValueError:
                                    pass
                            else:
                                Lf.<par> = NumberField(p1)
                                try:
                                    OTP = E.change_ring(Lf).lift_x(par)
                                    if p2(OTP[1]) == 0 or p2((-OTP)[1]) == 0:
                                        if p2.degree() == 1:
                                            points_new_torsion[i] = (p1, QQ(A[1]))
                                        else:
                                            points_new_torsion[i] = (p1, p2)
                                    else:
                                        continue
                                except ValueError:
                                    continue

                points_new_torsion_all_classes.extend(points_new_torsion)
                all_integral_points_torsion.extend(integral_points_torsion)
                count_extra_points_torsion += len(points_new_torsion)

                integral_points_non_torsion = []
                points_new_non_torsion = []
                points_non_torsion = [E.change_ring(K)(u^2*QP[0]+r,u^3*QP[1]+s*u^2*QP[0]+tt) for QP in points_non_torsion]
                for A in points_non_torsion:
                    try:
                        NIP = E.lift_x(QQ(A[0]))
                        if NIP[1] - A[1] == 0:
                            integral_points_non_torsion.append(NIP)
                        else:
                            NIP = -E(NIP[0],NIP[1])
                            integral_points_non_torsion.append(NIP)
                    except ValueError:
                        points_new_non_torsion.append(A)

                if points_new_non_torsion != []:
                    for A in points_new_non_torsion:
                        i = points_new_non_torsion.index(A)
                        p1 = algdep(A[0],2)
                        p2 = algdep(A[1],2)
                        if p1.is_irreducible() and p2.is_irreducible():
                            Lf.<par> = NumberField(p2)
                            if p1.degree() == 1:
                                try:
                                    OTP = E.change_ring(Lf).lift_x(QQ(A[0]))
                                    if p2(OTP[1]) == 0 or p2((-OTP)[1]) ==0:
                                        points_new_non_torsion[i] = (QQ(A[0]),p2)
                                except ValueError:
                                    pass
                            else:
                                Lf.<par> = NumberField(p1)
                                try:
                                    OTP = E.change_ring(Lf).lift_x(par)
                                    if p2(OTP[1]) == 0 or p2((-OTP)[1]) == 0:
                                        if p2.degree() == 1:
                                            points_new_non_torsion[i] = (p1,QQ(A[1]))
                                        else:
                                            points_new_non_torsion[i] = (p1,p2)
                                    else:
                                        continue
                                except ValueError:
                                    continue
                points_new_non_torsion_all_classes.extend(points_new_non_torsion)
                all_integral_points_non_torsion.extend(integral_points_non_torsion)
                count_extra_points_non_torsion += len(points_new_non_torsion)



    if torsion == False:
        all_integral_points.sort()
        points_new_all_classes.sort(key=sorting_fct)
        return all_integral_points, count_extra_points, points_new_all_classes
    else:
        all_integral_points_torsion.sort()
        all_integral_points_non_torsion.sort()
        points_new_torsion_all_classes.sort(key=sorting_fct)
        points_new_non_torsion_all_classes.sort(key=sorting_fct)
        return [all_integral_points_torsion, all_integral_points_non_torsion], [count_extra_points_torsion, count_extra_points_non_torsion], [points_new_torsion_all_classes, points_new_non_torsion_all_classes]

