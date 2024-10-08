from typing import Iterator

from homogeneous.bundle import BundleBWB
from homogeneous.variety import OGr, Quadric
from sage.combinat.integer_lists.invlex import IntegerListsLex
from sage.rings.integer_ring import ZZ

from bundle_collection.lefschetz import Construct_2D_by_rows, LefschetzCollection


def Kapranov(d: int) -> LefschetzCollection:
    """
    Returns Kapranov's full exceptional collection on the quadric Q^d.

    OUTPUT:
    - Full exceptional collection consisting of the exceptional orbit of O_Q
      and the spinor bundle S.

    REFERENCE:
    - [Kap1988] Kapranov, M. M.: On the derived categories of coherent sheaves
      on some homogeneous spaces. Invent. Math.92(1988), no.3, 479–508.
    """
    X = Quadric(d)
    n = X.cartan_rank()
    cartan_family = X.cartan_family()
    fano_index = X.fano_index()
    rows = []
    # Tautological subcollection
    rows += [(X.O(), fano_index)]
    # Spinor subcollection
    if cartan_family == "B":
        rows += [(X.S(), 1)]
    elif cartan_family == "D":
        rows += [(X.S("+"), 1), (X.S("-"), 1)]
    # Output
    output = Construct_2D_by_rows(X.O(1), rows)
    output._is_full = True
    return output


def Kuznetsov(N: int) -> LefschetzCollection:
    """
    Returns Kuznetsov's full exceptional collection on the OGr(2,N)
    where N is odd.

    OUTPUT:
    - Full exceptional collection consisting of a tautological subcollection
      and a spinor subcollection.

    REFERENCE:
    - [Kuz2008] Kuznetsov, A.: Exceptional collections for Grassmannians of
      isotropic lines. In: Proceedings of the London Mathematical Society 97.1
      (Mar. 2008), 155–182.
    """
    assert N in ZZ, "The input for `N` needs to be an integer."
    assert N % 2 == 1, "The integer `N` needs to be odd."
    X = OGr(2, N)  # Cartan family of type B.
    n = X.cartan_rank()
    fano_index = 2 * n - 2
    rows = []
    # Tautological subcollection
    rows += [(X.U().dual().sym(i), fano_index) for i in range(n - 1)]
    # Spinor subcollection
    rows += [(X.S(), fano_index)]
    # Output
    output = Construct_2D_by_rows(X.O(1), rows)
    output._is_full = True
    return output


def KuznetsovSmirnov(N: int) -> LefschetzCollection:
    """
    Returns full exceptional collection on the OGr(2,N) where N is even.

    OUTPUT:
    - Full exceptional collection consisting of a tautological subcollection
      and a spinor subcollection.

    REFERENCE:
    - [KuzSmi2020] Kuznetsov, A. and Smirnov, M.: Residual categories for
      (co)adjoint Grassmannians in classical types. In: Compositio Mathematica
      157.6 (May 2021)
    """
    assert N in ZZ, "The input for `N` needs to be an integer."
    assert N % 2 == 0, "The integer `N` needs to be even."
    X = OGr(2, N)  # Cartan family of type D.
    n = X.cartan_rank()
    fano_index = 2 * n - 3
    rows = []
    rows += [(X.S("-").sym(2)(-1), 1), (X.S("+").sym(2)(-1), 1)]
    rows += [(X.U().dual().sym(i), fano_index) for i in range(n - 2)]
    rows += [(X.U().dual().sym(n - 2), n - 1)]
    rows += [(X.S("-"), fano_index), (X.S("+"), fano_index)]
    output = Construct_2D_by_rows(X.O(1), rows)
    output = output.remove_object(n, (0,))  # Remove the object Sym^(n-2) U.dual
    output._is_full = True
    return output


def SpinorSubcollection(k: int, N: int) -> LefschetzCollection:
    X = OGr(k, N)
    n = X.cartan_rank()
    fano_index = 2 * n - k
    rows = []
    for d in range(n - 1):
        if d == 0:
            bdl = X.S()
            row_length = fano_index
        elif 1 <= d and d <= n - k:
            bdl = X.S() * X.U().dual().sym(d) + X.S() * X.U().dual().sym(d - 1)
            row_length = fano_index
        elif d == n - k + 1:
            bdl = X.S() * X.U().dual().sym(n - 2) + X.S() * X.U().dual().sym(n - 3)
            row_length = n - k + 1
        rows += [(bdl, row_length)]
    return Construct_2D_by_rows(X.O(1), rows)


def TautologicalSubcollection(k: int, N: int) -> LefschetzCollection:
    X = OGr(k, N)
    n = X.cartan_rank()
    fano_index = 2 * n - k
    weights = []
    # weights += [
    #    tuple(list(partition) + (n - 3) * [0])
    #    for partition in IntegerListsLex(
    #        length=3,
    #        floor=[n - 2, 0, 0],
    #        ceiling=[floor(3 / 2 * (n - 3)), ceil(1 / 2 * (n - 3)), 0],
    #        min_slope=-n + 3,
    #        max_slope=0,
    #    )
    # ]
    weights += [
        tuple(list(partition) + (n - k) * [0])
        for partition in IntegerListsLex(
            length=k, ceiling=(k - 1) * [n - k] + [0], max_slope=0
        )
    ]
    weights.reverse()
    rows = []
    for weight in weights:
        bdl = BundleBWB.from_tuple(X, weight, "ambt")
        row_length = fano_index
        rows += [(bdl, row_length)]
    return Construct_2D_by_rows(X.O(1), rows)
