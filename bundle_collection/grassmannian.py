from typing import Iterator

from homogeneous.bundle import BundleBWB
from homogeneous.variety import PP, Gr
from sage.combinat.integer_lists.invlex import IntegerListsLex
from young.diagrams import YoungDiagrams

from bundle_collection.lefschetz import Construct_2D_by_rows, LefschetzCollection


def Beilinson(d: int) -> LefschetzCollection:
    """
    Returns Beilinson's full exceptional collection on the projective space
    PP(n).

    OUTPUT:
    - Lefschetz collection with starting block ( O_X ) and support partition
      (d+1)*[ 1 ].

    REFERENCE:
    - [Bei1978] Beilinson, A. A.: Coherent sheaves on Pn and problems in linear
      algebra. Funktsional. Anal. i Prilozhen.12(1978), no.3, 68–69.
    """
    X = PP(d)
    output = Construct_2D_by_rows(X.O(1), [(X.O(), d + 1)])
    output._is_full = True
    return output


def Fonarev(k: int, N: int, label: str = "A") -> LefschetzCollection:
    """
    Returns Fonarev's (conjecturally full) minimal exceptional collection on
    the Grassmannian Gr(k,N).

    OUTPUT:
    - (Conjecturally full) minimal exceptional collection

    REFERENCE:
    - [Fon2012] Fonarev, A.: On minimal Lefschetz decompositions for Grass-
      mannians
    """
    X = Gr(k, N)
    n = X.cartan_rank()
    if label == "A":
        rows = []
        for YD in YoungDiagrams(N - k, k).get_minimal_upper_triangulars():
            weight = tuple(list(YD._usual_description) + (n - k) * [0])
            bdl = BundleBWB.from_tuple(X, weight, "ambt")
            row_length = YD.orbit_length()
            rows += [(bdl, row_length)]
        output = Construct_2D_by_rows(X.O(1), rows)
        return output
    elif label == "B":
        rows = []
        for YD in YoungDiagrams(N - k, k).get_upper_triangulars():
            weight = YD._usual_description
            bdl = BundleBWB.from_tuple(X, weight, "ambt")
            row_length = YD.r()  # The method r is not yet implemented!
            rows += [(bdl, row_length)]
        output = Construct_2D_by_rows(X.O(1), rows)
        output._is_full = True
        return output
    else:
        raise ValueError("There are tow labels, namely `A` or `B`.")


def Kapranov(k: int, N: int) -> LefschetzCollection:
    """
    Returns Kapranov's full exceptional collection on the Grassmannian Gr(k,N).

    OUTPUT:
    - Full exceptional collection cU^alpha
      with n-k => alpha_1 => alpha_2 => ... => alpha_k => 0 (lexicographically
      ordered)

    REFERENCE:
    - [Kap1988] Kapranov, M. M.: On the derived categories of coherent sheaves
      on some homogeneous spaces. Invent. Math.92(1988), no.3, 479–508.
    """
    X = Gr(k, N)
    n = X.cartan_rank()
    weights = [
        tuple(list(partition) + (n - k + 1) * [0])
        for partition in IntegerListsLex(length=k - 1, max_part=N - k, max_slope=0)
    ]
    weights.reverse()
    rows = []
    for weight in weights:
        bdl = BundleBWB.from_tuple(X, weight, "ambt")
        row_length = N - k + 1 - weight[0]
        rows += [(bdl, row_length)]
    output = Construct_2D_by_rows(X.O(1), rows)
    output._is_full = True
    return output


def TautologicalSubcollection(k: int, N: int) -> LefschetzCollection:
    X = Gr(k, N)
    n = X.cartan_rank()
    fano_index = n + 1
    weights = []
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
