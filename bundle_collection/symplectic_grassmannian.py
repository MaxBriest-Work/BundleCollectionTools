from typing import Iterator

from homogeneous.bundle import BundleBWB
from homogeneous.variety import SGr

from bundle_collection.lefschetz import Construct_2D_by_rows, LefschetzCollection

# from sage.combinat.integer_lists.invlex import IntegerListsLex


def Kuznetsov(N: int) -> LefschetzCollection:
    """
    Returns Kuznetsov's full exceptional collection on the SGr(2,N).

    OUTPUT:
    - Full exceptional collection arising by a hyperplane section of Gr(2,N).

    REFERENCE:
    - [Kuz2008] Kuznetsov, A.: Exceptional collections for Grassmannians of
      isotropic lines. In: Proceedings of the London Mathematical Society 97.1
      (Mar. 2008), 155–182.
    """
    X = SGr(2, N)  # Cartan family of type C.
    n = X.cartan_rank()
    fano_index = 2 * n - 1
    rows = []
    # Tautological subcollection
    rows += [(X.U().dual().sym(i), fano_index) for i in range(n - 1)]
    rows += [(X.U().dual().sym(n - 1), n - 1)]
    # Output
    output = Construct_2D_by_rows(X.O(1), rows)
    output._is_full = True
    return output
