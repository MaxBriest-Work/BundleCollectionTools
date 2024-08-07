from typing import Iterator

from homogeneous import *
from sage.calculus.var import var
from sage.combinat.integer_lists.invlex import IntegerListsLex
from sage.functions.other import ceil, floor
from sage.matrix.constructor import matrix
from sage.misc.table import table
from sage.modules.free_module_element import vector
from sage.rings.abc import SymbolicRing
from sage.rings.integer_ring import ZZ
from sage.rings.rational_field import QQ
from sage.structure.element import Expression


class LefschetzCollection(object):

    def __add__(self, other) -> "LefschetzCollection":
        """
        Add/ merge to Lefschetz collection.
        Caution: The process is not commutative.
        """
        # 1) Test if `other` is likewise a Lefschetz collection.
        assert isinstance(
            other, LefschetzCollection
        ), "The input for `other` needs to be likewise a Lefschetz collection."
        # 2) Test if the twists of both Lefschetz collecitons coincide.
        assert (
            self._twists == other._twists
        ), "The twists of both Lefschetz collections needs to coincide."
        # 3) Add/merge both collections.
        # 3.1) Attach the starting block of `other` to the one of `self`.
        starting_block = self._starting_block + other._starting_block
        # 3.2) Keep the twists.
        twists = self._twists
        # 3.3) Attach the support of `other` to the one of `self`. Therefore, shift
        #      those points in the support where the corresponding bundles in the start-
        #      ing are shifted in 3.1.
        #      Note: The lexicographical order will be ensured later when we initialise
        #            from this data the Lefschetz collection.
        shift = len(self._starting_block)
        support = self._support + [
            tuple([point[0] + shift] + list(point[1:])) for point in other._support
        ]
        # We are finished. Initialise the Lefschetz collection from the new data.
        return LefschetzCollection(starting_block, twists, support)

    def __contains__(self, other) -> bool:
        # TODO: Implement method to test if a Lefschetz collection contains some other
        #      one.
        raise NotImplementedError()

    def __getitem__(self, arg: int or slice) -> BundleBWB or list[BundleBWB]:
        """
        Returns a single objects or a slice from `self`.
        """
        # 1) Test if the input is a single integer.
        #    Yes: Take the corresponding support point and get the appropriate object.
        if arg in ZZ:
            point = self._support[arg]
            return self.get_object(point[0], point[1:])
        # 2) Test if the input is a slice.
        #    Yes: Take the corresponding support points and get the appropriate objects.
        elif isinstance(arg, slice):
            points = self._support[arg]
            return [self.get_object(point[0], point[1:]) for point in points]
        # 3) If we have had always no in the previous tests, then we do not understand
        #    the input.
        else:
            raise ValueError("We do not understand the passed argument.")

    def __init__(
        self,
        starting_block: list[BundleBWB],
        twists: list[BundleBWB],
        support: list[vector],
    ) -> None:
        """
        Initialise a Lefschetz collection.
        """
        # 1) Initialise a starting block of bundles over a common base space.
        self._starting_block = []
        self._base_space = None
        # 1.1) Test if the starting block is given as list.
        assert isinstance(
            starting_block, list
        ), "The starting block needs to be given as list."
        # 1.2) Run over the list `starting_block` and consider its objects.
        for object_index, bundle in enumerate(starting_block):
            # 1.2.1) Test if the i-th object is a bundle in the BWB-format.
            assert isinstance(
                bundle, BundleBWB
            ), "The {i}-th bundle in the starting block needs to be a homogeneous bundle in BWB-format.".format(
                i=object_index
            )
            # 1.2.2) If we consider the first bundle, then store its base space as
            #        common one. Otherwise, if we consider the second/third/fourth/...
            #        bundle, then check if their base spaces coincide with the common
            #        one.
            if object_index == 0:
                self._base_space = bundle._base_space
            else:
                assert (
                    bundle._base_space == self._base_space
                ), "The {i}-th bundle in the starting block does not live over the common base space of the previous bundle(s).".format(
                    i=object_index
                )
            # 1.2.3) Attach the current bundle as further one to the attribute
            #        `_starting_block`.
            self._starting_block += [bundle]
        self._x = var("x")
        # 2) Initialise a list of twists (= line bundles over the common base space).
        self._twists = []
        # 2.1) Test if the twists are given as list.
        assert isinstance(twists, list), "The twists needs to be a given as list."
        # 2.2) Run over the list `twists` and consider its objects.
        for twist_index, twist in enumerate(twists):
            # 2.2.1) Test if the i-th object is a bundle in the BWB-format.
            assert isinstance(
                twist, BundleBWB
            ), "The {i}-th twist needs to be a homogeneous bundle in BWB-format.".format(
                i=twist_index
            )
            # 2.2.2) Test if the i-th bundle is a line bundle.
            #        In the following just called a twist.
            assert (
                twist.is_line_bundle()
            ), "The {i}-th twist needs to be a line bundle.".format(i=twist_index)
            # 2.2.3) Test if the base spaces of i-th twist coincides with the common
            #        base space.
            assert (
                twist._base_space == self._base_space
            ), "The {i}-th twist does not live over the common base space.".format(
                i=twist_index
            )
            # 2.2.4) Attach the current twist as further one to the attribute `_twists`.
            self._twists += [twist]
        # 2.3) The starting block admits the first direction and then each twist gives a
        #      a new direction. This means, the dimension is one plus the number of
        #      twists.
        self._dimension = 1 + len(self._twists)
        if 1 < self._dimension:
            self._t = var(
                ",".join(
                    [
                        "t{p}".format(p=position)
                        for position in range(1, self._dimension)
                    ]
                )
            )
        else:
            self._t = None
        # 3) Initialise the support
        self._support = []
        # 3.1) For each direction, we store in `_sizes` the minimum and the maximum of
        #      the extent.
        self._sizes = self._dimension * [(None, None)]
        # 3.2) Store each object index which appears at least once; i.e. the object is
        #      alive.
        alive = []
        # 3.3) Test if the support is given as list.
        assert isinstance(support, list), "The support needs to be a list."
        # 3.4) Test if there are support points and therefore we ensure that not empty
        #      arguments are passed to minimum- and maximum-functions.
        if 0 < len(support):
            # 3.4.1) If the support is non-empty, run over the list `support` and consi-
            #        der its objects.
            for point in support:
                # 3.4.1.1) Test if a support point is given as tuple.
                assert isinstance(point, tuple), "The support points need to be tuples."
                # 3.4.1.2) Test if a support point has length d (d=dimension).
                assert (
                    len(point) == self._dimension
                ), "The support points need to be of length {d}.".format(
                    d=self._dimension
                )
                # 3.4.1.3) Given a support point, run over its entries.
                for position, entry in enumerate(point):
                    # 3.4.1.3.1) The first entry corresponds to a object of the starting
                    #            block. Hence, it needs to be in the range(l) where l is
                    #            the length of the starting block.
                    #            The remaining entries correspond to twists. Hence, they
                    #            need to be integers.
                    if position == 0:
                        assert entry in range(
                            len(self._starting_block)
                        ), "For a given support point, the first entry needs to be in the range from 0 to {l}.".format(
                            l=len(self._starting_block)
                        )
                        #        Store every object index which appears at least once in
                        #        the support.
                        if not entry in alive:
                            alive += [entry]
                    else:
                        assert (
                            entry in ZZ
                        ), "For a given support point, the entries need to be integers."
                    # 3.4.1.3.2) For the p-th direction, converge to minimal and maximal
                    #            extent. This means, take the minimal and maximal values
                    #            detected so far, compare with the current value and
                    #            converge to the final minimal and maximal values.
                    old_minimum, old_maximum = self._sizes[position]
                    if (
                        old_minimum,
                        old_maximum,
                    ) == (
                        None,
                        None,
                    ):
                        new_minimum = entry
                        new_maximum = entry
                    else:
                        new_minimum = min([old_minimum, entry])
                        new_maximum = max([old_maximum, entry])
                    self._sizes[position] = (
                        new_minimum,
                        new_maximum,
                    )
            # 3.4.2) Bring the support points in lexicographical order (i.e. from low to
            #        high).
            # 3.4.2.1) The shift describes the vector from the origin to point with mi-
            #          nimal entries. This is necessary as `IntegerListsLex` runs over
            #          non-negative integer lists.
            shift = vector(ZZ, [minimum for minimum, maximum in self._sizes][::-1])
            # 3.4.2.2) Run over all non-negative integer points with entries bounded by
            #          the appropriated maximal extent in the reversed lexicographical
            #          order (i.e. from higher to lower).
            for point in IntegerListsLex(
                length=len(self._sizes),
                ceiling=[maximum - minimum for minimum, maximum in self._sizes][::-1],
            ):
                # Shift the point.
                # Store its entries reversely.
                point = tuple(list(vector(ZZ, list(point)) + shift)[::-1])
                # Test if the point is in the support. If yes, then attach it to the
                # attribute `_support`.
                if point in support:
                    self._support += [point]
            # 3.4.2.3) Reverse the order due to reversed lexicographical order of
            #          `IntegerListsLex`.
            self._support.reverse()
        # 4) If the starting block contains dead objects, i.e. objects which are not
        #    supported, then we drop this from the starting block and the support.
        alive.sort()
        if len(alive) < len(self._starting_block):
            self._starting_block = [
                bdl
                for object_index, bdl in enumerate(self._starting_block)
                if object_index in alive
            ]
            translation = {
                old_index: new_index for new_index, old_index in enumerate(alive)
            }
            self._support = [
                tuple([translation[point[0]]] + list(point[1:]))
                for point in self._support
            ]
        # 5) Initialise a bunch of auxiliary attributes.
        # 5.1) If the Gram matrix has been computed, then we store the result in
        #      `_gram_matrix`.
        self._gram_matrix = None
        # 5.2) If it has been checked whether `self` is (numerically) exceptional, then
        #      we store the result in `_is_exceptional` or `_is_numerically_exceptional`
        #      respectively.
        self._is_exceptional = None
        self._is_numerically_exceptional = None
        # 5.3) If it is known that `self` is full, then one can store a corresponding
        #      boolean value.
        self._is_full = None
        # 5.4)
        self._semiorthogonal_relations = None

    def __iter__(self) -> Iterator[BundleBWB]:
        """
        Run over the objects of `self`.
        """
        return (
            self.get_object(support_point[0], support_point[1:])
            for support_point in self._support
        )

    def __len__(self) -> int:
        """
        Returns the length of `self`, i.e. the number of objects.
        """
        return len(self._support)

    def __repr__(self) -> tuple:
        """
        Returns a developer-friendly description of `self`.
        """
        return self._starting_block, self._twists, self._support

    def __str__(self) -> str:
        """
        Returns a user-friendly description of `self`.
        """
        return "Lefschetz collection of {l} objects over {bs}.".format(
            l=len(self), bs=self._base_space.as_string()
        )

    def blow_up(self, new_twist: BundleBWB, extension: tuple) -> "LefschetzCollection":
        """
        Returns a user-friendly description of `self`.
        """
        # 1) Various tests on the input `new_twist`.
        # 1.1) Test if the new twist is a bundle in the BWB-format.
        assert isinstance(
            new_twist, BundleBWB
        ), "The twist needs to be a homogeneous bundle in the BWB-format."
        # 1.2) Test if the base space of the new twist coincides with the common base
        #    space.
        assert (
            new_twist._base_space == self._base_space
        ), "The twist needs to live over the common base space."
        # 1.3) Test if the new twist is a line bundle.
        assert new_twist.is_line_bundle(), "The twist needs to be a line bundle."
        # 2) Various tests on the input `extension`.
        # 2.1) Test if the new support is given as tuple.
        assert isinstance(
            extension, tuple
        ), "The new support needs to be give as tuple."
        # 2.2) Test if the new support is non-empty.
        assert 0 < len(extension), "The new support needs to cointain entries."
        # 2.3) Test if the new support consists of integers.
        for index, entry in enumerate(extension):
            assert (
                entry in ZZ
            ), "The {i}-th entry in the new support needs to be an integer.".format(
                i=index
            )
        # 2.4) Prepare the input `extension`.
        #      set: No doubles
        #      sorted: Sorted entries from low to high
        extension = tuple(sorted(list(set(extension))))
        # 3) Form data for new Lefschetz collection
        # 3.1) Extend the current twists by the new one.
        twists = self._twists + [new_twist]
        # 3.2) Extend the support points.
        support = [
            tuple(list(old_point) + [entry])
            for old_point in list(self._support)
            for entry in extension
        ]
        # We are finished.
        return LefschetzCollection(self._starting_block, twists, support)

    def extend_starting_block_by_object(self, bdl: BundleBWB) -> Iterator[tuple]:
        """
        Given a bundle `bdl`, test if `self` can be extended and return an iterator for
        all possible support points.
        """
        assert isinstance(
            bdl, BundleBWB
        ), "The input for `bdl` needs to be a homogeneous bundle in BWB-format."
        raise NotImplementedError()

    def get_semiorthogonal_relations_for_object(
        self, object_index: int, twisting: tuple[int]
    ) -> Iterator:
        # 1) Test if the object index is an integer.
        assert object_index in ZZ, "The object index needs to be an integer."
        # 2) Test if the twisting is a tuple of length d-1 (d=dimension).
        assert isinstance(twisting, tuple), "The twisting needs to be given as tuple."
        assert (
            len(twisting) == self._dimension - 1
        ), "The number of twists needs to be {c}.".format(c=self._dimension - 1)
        # 3) Form the corresponding point.
        point = tuple([object_index] + list(twisting))
        # 4) Test if the point lies in the support.
        #    Yes: Go on and find corresponding semiorthogonal relations.
        #    No : No semiorthogonal relations appear.
        if point in self._support:
            # As we start at the beginning of the support, we are before our point.
            relative_position = "before"
            # 4.1) Run over the support.
            for other in self._support:
                # 4.1.1) If we are before our point, return (other,point).
                if relative_position == "before":
                    x1 = other[0]
                    t1 = other[1:]
                    x2 = point[0]
                    t2 = point[1:]
                    if other == point:
                        relative_position = "after"
                # 4.1.2) If we are after our point, return (point,other).
                else:
                    x1 = point[0]
                    t1 = point[1:]
                    x2 = other[0]
                    t2 = other[1:]
                yield (
                    x1,
                    t1,
                ), (
                    x2,
                    t2,
                )

    def get_semiorthogonal_relations(self) -> Iterator:
        if self._semiorthogonal_relations == None:
            semiorthogonal_relations = dict({})
            for point1 in self._support:
                x = point1[0]
                t = point1[1:]
                for (x1, t1), (x2, t2) in self.get_semiorthogonal_relations_for_object(
                    x, t
                ):
                    if not (x1, x2) in semiorthogonal_relations.keys():
                        semiorthogonal_relations.update({(x1, x2): []})
                    difference = tuple(vector(ZZ, t2) - vector(ZZ, t1))
                    if not difference in semiorthogonal_relations[(x1, x2)]:
                        semiorthogonal_relations[(x1, x2)] += [difference]
            self._semiorthogonal_relations = semiorthogonal_relations
        zero = tuple((self._dimension - 1) * [0])
        for x1, x2 in self._semiorthogonal_relations.keys():
            for difference in self._semiorthogonal_relations[(x1, x2)]:
                yield (x1, zero), (x2, difference)

    def get_object(self, object_index: int, twisting: tuple[int]) -> BundleBWB:
        """
        Returns a selected object of `self`.
        """
        # 1) Test if the object index is an integer.
        assert object_index in ZZ, "The object index needs to be an integer."
        # 2) Test if the twisting is a tuple of length d-1 (d=dimension).
        assert isinstance(twisting, tuple), "The twisting needs to be given as tuple."
        assert (
            len(twisting) == self._dimension - 1
        ), "The number of twists needs to be {c}.".format(c=self._dimension - 1)
        # 3) Form the corresponding point.
        point = tuple([object_index] + list(twisting))
        # 4) Test if the point lies in the support.
        #    Yes: Construct the corresponding object
        if point in self._support:
            output = self._starting_block[object_index]
            for position, exponent in enumerate(twisting):
                output *= self._twists[position] ** exponent
        #    No : Return the zero bundle.
        else:
            output = self._base_space.zero_bundle()
        # We are finished.
        return output

    def get_subcollection(self, *equations) -> "LefschetzCollection":
        """
        Returns a subcollection with respect to a family of equations.
        """
        # 1) Test if the input for `equations` are expressions.
        for index, equation in enumerate(equations):
            assert isinstance(
                equation, Expression
            ), "The {i}-th equation needs to be an expression.".format(i=index)
        # 2) Collect the remaining support points satisfying the bunch of equations.
        #    Run over the set of support points and evaluate each equation at this
        #    point. If each equation holds, then keep the point as support point.
        support = [
            support_point
            for support_point in self._support
            if not False
            in [
                bool(
                    equation(
                        dict(
                            {
                                variable: value
                                for variable, value in zip(
                                    self.parameters(), support_point
                                )
                            }
                        )
                    )
                )
                for equation in equations
            ]
        ]
        return LefschetzCollection(self._starting_block, self._twists, support)

    def gram_matrix(self) -> "matrix":
        """
        Returns the Gram matrix of `self`.
        The entry in the p-th row and q-th column computes as
           sum_{i} (-1)^i Ext^i( E_p , E_q ).
        """
        # Test if the attribute `_gram_matrix` is None.
        # Yes: The method has not run yet.
        if self._gram_matrix == None:
            self._gram_matrix = matrix(
                self._base_space._WCR,
                [
                    [(E1.dual() * E2).euler_characteristic() for E2 in self]
                    for E1 in self
                ],
            )
        # Return the stored result.
        return self._gram_matrix

    def is_exceptional(self) -> bool:
        """
        Test if self is exceptional.
        """
        # 1) Test if the attribute `_is_exceptional` is None.
        #    Yes: The method has not run yet.
        if self._is_exceptional == None:
            # 2) Test if the attribute `_is_numerically_exceptional` is False.
            #    Yes: `self` is not numerically exceptional and therefore it can not be
            #         exceptional.
            if self._is_numerically_exceptional == False:
                self._is_exceptional = False
            #    No : Run the method.
            else:
                # 3) Run over the set of necessary semiorthogonal relations:
                for (x1, t1), (x2, t2) in self.get_semiorthogonal_relations():
                    # 3.1) Test if each object is exceptional.
                    if x1 == x2 and t1 == t2:
                        E = self.get_object(x1, t1)
                        if E.is_exceptional() == False:
                            self._is_exceptional = False
                            break
                    # 3.2) Test if there are no morphims from hight to low.
                    else:
                        E1 = self.get_object(x1, t1)
                        E2 = self.get_object(x2, t2)
                        if E2.is_semiorthogonal_to(E1) == False:
                            self._is_exceptional = False
                            break
                # 4) If we reach this point, then all semiorthogonal relations are sa-
                #    tisfied. Hence, `self` needs to be exceptional.
                if self._is_exceptional == None:
                    self._is_exceptional = True
        # Return the stored result.
        return self._is_exceptional

    def is_full(self) -> bool:
        """
        Test if self is known to be full.
        """
        if self._is_full == None:
            if len(self) < self._base_space.euler_characteristic():
                self._is_full = False
        return self._is_full

    def is_numerically_exceptional(self) -> bool:
        """
        Test if self is numerically exceptional.
        """
        # 1) Test if the attribute `_is_numerically_exceptional` is None.
        #    Yes: The method has not run yet.
        if self._is_numerically_exceptional == None:
            # 2) Test if the attribute `_is_exceptional` is True.
            #    Yes: `self` is exceptional and therefore needs to be likewise numer-
            #         ically exceptional.
            if self._is_exceptional == True:
                self._is_numerically_exceptional = True
            #    No : Run the method.
            else:
                # 3) Run over the set of necessary semiorthogonal relations:
                for (x1, t1), (x2, t2) in self.get_semiorthogonal_relations():
                    # 3.1) Test if each object is exceptional.
                    if x1 == x2 and t1 == t2:
                        E = self.get_object(x1, t1)
                        E.is_numerically_exceptional()
                    # 3.2) Test if there are no morphims from hight to low.
                    else:
                        E1 = self.get_object(x1, t1)
                        E2 = self.get_object(x1, t1)
                        E2.is_numerically_semiorthogonal_to(E1)
                # 4) If we reach this point, then all semiorthogonal relations are sa-
                #    tisfied numerically. Hence, `self` needs to be numerical exception-
                #    al.
                if self._is_numerically_exceptional == None:
                    self._is_numerically_exceptional = True
        # Return the stored result.
        return self._is_numerically_exceptional

    def is_of_maximal_expected_length(self) -> bool:
        """
        Test if self is of maximal expected length.
        """
        return len(self) == self._base_space.euler_characteristic()

    def parameters(self) -> tuple["variables"]:
        """
        Returns the parameters `x` and `t` as combined tuple.
        """
        if self._dimension == 0:
            return tuple([])
        elif self._dimension == 1:
            return tuple([self._x])
        elif self._dimension == 2:
            return tuple([self._x, self._t])
        else:
            return tuple([self._x] + list(self._t))

    def remove_object(
        self, object_index: int, twisting: tuple[int]
    ) -> "LefschetzCollection":
        """
        Remove an object from the support.
        """
        # 1) Test if the object index is an integer.
        assert object_index in ZZ, "The object index needs to be an integer."
        # 2) Test if the twisting is given as tuple of length d-1 (d=dimension).
        assert isinstance(twisting, tuple), "The twists needs to be given as tuple."
        assert (
            len(twisting) == self._dimension - 1
        ), "The number of twists needs to be {c}.".format(c=self._dimension - 1)
        # 3) Form a point from the input.
        point = tuple([object_index] + list(twisting))
        # 4) Test if the point lies in the support.
        #    Yes: Remove the point from the support and initialise a Lefschetz collec-
        #         tion from the new data.
        #    No : Return the old Lefschetz collection.
        if point in self._support:
            support = self._support
            support.remove(point)
            return LefschetzCollection(self._starting_block, self._twists, support)
        else:
            return self

    def show_layer(self) -> table:
        """
        Returns a table showing the objects in a grid.
        """
        # Test if the support is empty.
        # Yes: Return empty table.
        if len(self._support) == 0:
            body = [[]]
            return table(body)
        # No : Go on.
        else:
            # 1) Find directions where we can extent.
            directions_to_extent = tuple(
                [
                    position
                    for position, (minimum, maximum) in enumerate(self._sizes)
                    if minimum < maximum
                ]
            )
            # Dimension 0
            # There is no free direction. However, the support is not empty. Hence, the
            # there needs to be an unique point.
            if len(directions_to_extent) == 0:
                # Logical test if there is a unique support point.
                assert (
                    len(self._support) == 1
                ), "There are now directions to extent. Hence, there needs to be a unique support point."
                x = self._support[0][0]
                twisting = self._support[0][1:]
                if len(twisting) == 0:
                    body = [["E{x}".format(x=x)]]
                else:
                    body = [["E{x}{t}".format(x=x, t=twisting)]]
                return table(body)
            # Dimension 1
            # There is one free direction.
            elif len(directions_to_extent) == 1:
                (position1,) = directions_to_extent
                range1 = range(self._sizes[position1][0], self._sizes[position1][1] + 1)
                # If we run in x-direction, then each new object gives a new column.
                if position1 == 0:
                    body = []
                    for x in range1:
                        twisting = [
                            minimum
                            for position, (minimum, maximum) in enumerate(self._sizes)
                            if 0 < position
                        ]
                        point = tuple([x] + twisting)
                        if point in self._support:
                            if len(twisting) == 0:
                                body += [["E{x}".format(x=x)]]
                            else:
                                body += [
                                    [
                                        "E{x}({t})".format(
                                            x=x,
                                            t=",".join(
                                                [str(exponent) for exponent in twisting]
                                            ),
                                        )
                                    ]
                                ]
                        else:
                            body += [[""]]
                # If we run in some t-direction, then each new object is part of the
                # same row (= orbit).
                else:
                    x = self._sizes[0][0]
                    twisting_before = [
                        minimum
                        for position, (minimum, maximum) in enumerate(self._sizes)
                        if 0 < position and position < position1
                    ]
                    twisting_after = [
                        minimum
                        for position, (minimum, maximum) in enumerate(self._sizes)
                        if position1 < position
                    ]
                    row = []
                    for value in range1:
                        twisting = twisting_before + [value] + twisting_after
                        point = tuple([x] + twisting)
                        if point in self._support:
                            row += [
                                "E{x}({t})".format(
                                    x=x,
                                    t=",".join(
                                        [str(exponent) for exponent in twisting]
                                    ),
                                )
                            ]
                        else:
                            row += [""]
                    body = [row]
                return table(body)
            # Dimension 2
            # There are two free directions. Hence, the first directions gives rows and
            # the second one columns.
            elif len(directions_to_extent) == 2:
                (
                    position1,
                    position2,
                ) = directions_to_extent
                range1 = range(self._sizes[position1][0], self._sizes[position1][1] + 1)
                range2 = range(self._sizes[position2][0], self._sizes[position2][1] + 1)
                before = [
                    minimum
                    for position, (minimum, maximum) in enumerate(self._sizes)
                    if position < position1
                ]
                mid = [
                    minimum
                    for position, (minimum, maximum) in enumerate(self._sizes)
                    if position1 < position and position < position2
                ]
                after = [
                    minimum
                    for position, (minimum, maximum) in enumerate(self._sizes)
                    if position2 < position
                ]
                body = []
                for value1 in range1:
                    row = []
                    for value2 in range2:
                        point = tuple(before + [value1] + mid + [value2] + after)
                        x = point[0]
                        twisting = point[1:]
                        if point in self._support:
                            row += [
                                "E{x}({t})".format(
                                    x=x,
                                    t=",".join(
                                        [str(exponent) for exponent in twisting]
                                    ),
                                )
                            ]
                        else:
                            row += [""]
                    body += [row]
                return table(body)
            # Dimension 3, 4, ...
            # There are more than two directions. We can not print a 2D-table from this.
            else:
                return (
                    "CAUTION: Can not print a layer for more than two free directions."
                )


# General constructors


def Construct_2D_by_rows(
    twist: BundleBWB, rows: list[tuple[BundleBWB, int]]
) -> LefschetzCollection:
    assert isinstance(rows, list), "The input for `rows` needs to be a list."
    twists = [twist]
    starting_block = []
    support = []
    for index, row in enumerate(rows):
        assert isinstance(row, tuple), "The input for {i}-th row needs to be a tuple."
        assert len(row) == 2, "The {i}-th row needs to be a tuple of length 2."
        bundle, row_length = row
        assert row_length in ZZ, "The {i}-th row length needs to be an integer."
        assert 0 <= row_length, "The {i}-th row length needs to be non-negative."
        starting_block += [bundle]
        support += [
            (
                index,
                i,
            )
            for i in range(row_length)
        ]
    return LefschetzCollection(starting_block, twists, support)


# Concrete examples


def Beilinson(n: int) -> LefschetzCollection:
    """
    Returns Beilinson's full exceptional collection on the projective space PP(n).

    OUTPUT:
    - Lefschetz collection with starting block ( O_X ) and support partition
      (n+1)*[ 1 ].

    REFERENCE:
    - [Bei1978] Beilinson, A. A.: Coherent sheaves on Pn and problems in linear algebra.
      Funktsional. Anal. i Prilozhen.12(1978), no.3, 68–69.
    """
    X = variety.PP(n)
    output = Construct_2D_by_rows(X.O(1), [(X.O(), n + 1)])
    output._is_full = True
    return output


def Fonarev(k: int, N: int) -> LefschetzCollection:
    """
    Returns Fonarev's (conjecturally full) minimal exceptional collection on the Grass-
    mannian Gr(k,N).

    OUTPUT:
    - (Conjecturally full) minimal exceptional collection

    REFERENCE:
    - [Fon2012] Fonarev, A.: On minimal Lefschetz decompositions for Grassmannians
    """
    raise NotImplementedError()
    # X = variety.Gr(k,N)
    # output = Empty_Collection()
    # for young_diagram , orbit_length in YoungDiagram.minimal_upper_triangulars( N-k , k ) :
    #    bdl = X.bdl( YD )
    #    row_length = orbit_length
    #    rows += [ (bdl, row_length ) ]
    # return Construct_2D_by_rows( X.O(1), rows )


def Kapranov(k: int, N: int) -> LefschetzCollection:
    """
    Returns Kapranov's full exceptional collection on the Grassmannian Gr(k,N).

    OUTPUT:
    - Full exceptional collection cU^alpha with n-k => alpha_1 => alpha_2 => ... =>
      alpha_k => 0 (lexicographically orderd)

    REFERENCE:
    - [Kap1988] Kapranov, M. M.: On the derived categories of coherent sheaves on some
      homogeneous spaces. Invent. Math.92(1988), no.3, 479–508.
    """
    X = variety.Gr(k, N)
    n = X.cartan_rank()
    weights = [
        tuple(list(partition) + (n - k + 1) * [0])
        for partition in IntegerListsLex(length=k - 1, max_part=N - k, max_slope=0)
    ]
    weights.reverse()
    rows = []
    for weight in weights:
        bdl = bundle.BundleBWB.from_tuple(X, weight, "ambt")
        row_length = N - k + 1 - weight[0]
        rows += [(bdl, row_length)]
    output = Construct_2D_by_rows(X.O(1), rows)
    output._is_full = True
    return output


def KuznetsovPolishchuk(base_space) -> Iterator[tuple[int, int, int, "weight", str]]:
    """
    Returns the collection of Kuznetsov and Polishchuk on X=G/P.

    INPUT:
    - `base_space` -- PartialFlagVariety; Homogeneous variety.

    OUTPUT:
    - `block_index` -- Integer; block index.
    - `highest_weight` -- highest weight of object.
    - `descriptoin` -- string description of cE(Lambda).

    REFERENCE:
    - [KP2016] Kuznetsov, Alexander; Polishchuk, Alexander Exceptional collections on
      isotropic Grassmannians. J. Eur. Math. Soc. (JEMS) 18 (2016), no. 3, 507–574.
    """
    # TODO: Implement collection for exceptional cases.
    assert isinstance(
        base_space, PartialFlagVariety
    ), "The input for `base_space` needs to be a partial flag variety."
    assert (
        base_space.is_generalized_grassmannian()
    ), "The method is only implemented for generalized Grassmannians; i.e. irreducible and maximal parabolic subgroup."
    cartan_family = base_space.cartan_family()
    n = base_space.cartan_rank()
    k = base_space.k()
    blocks = dict({})
    # Conjecture 9.8. on page 49
    if cartan_family == "A":
        l = n + 1 - k
        # Collect all intersection points between a line segment from (0,0) to (k,l) and
        # a grid { (x,y) : x \in ZZ or y \in ZZ }
        slope = l / k
        Q = []
        for x1 in range(k + 1):
            y1 = slope * x1
            Q += [(x1, y1)]
            if x1 < k:  # Notice: 0 < slope = (n+1)/k - 1 if and only if k < n+1
                Q += [
                    (y2 / slope, y2)
                    for y2 in range(ceil(y1), floor(y1 + slope) + 1)
                    if y1 < y2 and y2 < y1 + slope
                ]
        for t, (x, y) in enumerate(Q):
            a = floor(x)
            b = floor(y)
            c = k - ceil(x)
            d = l - ceil(y)
            block = [
                tuple(
                    list(p1)
                    + (k - a) * [t]
                    + (n + 1 - b - k) * [0]
                    + list(vector(ZZ, p2) - vector(ZZ, b * [c]))
                )
                for p2 in IntegerListsLex(length=b, min_part=0, max_part=c, max_slope=0)
                for p1 in IntegerListsLex(
                    length=a, min_part=t, max_part=d + t, max_slope=0
                )
            ]
            block.reverse()
            blocks.update({t: block})
    elif cartan_family == "B" or cartan_family == "D":
        # Equation 56 on page 39
        if cartan_family == "B":
            e = 1 / 2
        elif cartan_family == "D":
            e = 0
        # k <= n-1 if Cartan family is B or k <= n-2 if Cartan family is D
        # Theorem 9.1. on page 42
        if k in range(1, ZZ(n + 2 * e - 1)):
            for t in range(k):
                block = []
                for p1 in IntegerListsLex(
                    length=t, min_part=t, max_part=2 * n + 2 * e - k - 2, max_slope=0
                ):
                    for p2 in IntegerListsLex(
                        length=n - k,
                        min_part=0,
                        max_part=2 * floor((k - t) / 2),
                        max_slope=0,
                    ):
                        p2 = vector(ZZ, list(p2)) - vector(
                            ZZ, (n - k) * [floor((k - t) / 2)]
                        )
                        highest_weight = tuple(list(p1) + (k - t) * [t] + list(p2))
                        if highest_weight[n - 1] >= (2 * e - 1) * highest_weight[n - 2]:
                            block += [highest_weight]
                block.reverse()
                blocks.update({t: block})
                block = []
                for p1 in IntegerListsLex(
                    length=t, min_part=t, max_part=2 * n + 2 * e - k - 2, max_slope=0
                ):
                    for p2 in IntegerListsLex(
                        length=n - k,
                        min_part=0,
                        max_part=floor((k - t) / 2 - 1 / 2)
                        + floor((k - t) / 2 + 1 / 2),
                        max_slope=0,
                    ):
                        p2 = vector(ZZ, list(p2)) - vector(
                            ZZ, (n - k) * [floor((k - t) / 2 + 1 / 2)]
                        )
                        highest_weight = tuple(
                            vector(QQ, list(p1) + (k - t) * [t] + list(p2))
                            + vector(QQ, n * [1 / 2])
                        )
                        if highest_weight[n - 1] >= (2 * e - 1) * highest_weight[n - 2]:
                            block += [highest_weight]
                block.reverse()
                blocks.update({t + 1 / 2: block})
            for t in range(k, ZZ(2 * n + 2 * e - k - 1)):
                block = [
                    tuple(list(p1) + [t] + (n - k) * [0])
                    for p1 in IntegerListsLex(
                        length=k - 1,
                        min_part=t,
                        max_part=2 * n + 2 * e - k - 2,
                        max_slope=0,
                    )
                ]
                block.reverse()
                blocks.update({t: block})
        # k == n if Cartan family is B or k from { n-1 , n } if Cartan family is D
        # Theorem 9.3. on page 43
        elif k in range(ZZ(n + 2 * e - 1), n + 1):
            # D_n/P_n-1 and D_n/P_n are both isomorphic to B_n-1/P_n-1
            if cartan_family == "D":
                base_space = variety.OGr(n - 1, 2 * n - 1)
                cartan_family = base_space.cartan_family()
                n = base_space.cartan_rank()
                k = base_space.k()
            for t in range(n):
                block = [
                    tuple(list(p1) + (n - t) * [t])
                    for p1 in IntegerListsLex(
                        length=t, min_part=t, max_part=n - 1, max_slope=0
                    )
                ]
                block.reverse()
                blocks.update({2 * t: block})
                blocks.update(
                    {
                        2 * t
                        + 1: [
                            tuple(vector(QQ, highest_weight) + vector(QQ, n * [1 / 2]))
                            for highest_weight in blocks[2 * t]
                        ]
                    }
                )
    # Theorem 9.2. on page 42
    elif cartan_family == "C":
        for t in range(k):
            block = [
                tuple(list(p1) + (k - t) * [t] + list(p2))
                for p2 in IntegerListsLex(
                    length=n - k, min_part=0, max_part=floor((k - t) / 2), max_slope=0
                )
                for p1 in IntegerListsLex(
                    length=t, min_part=t, max_part=2 * n - k, max_slope=0
                )
            ]
            block.reverse()
            blocks.update({t: block})
        for t in range(k, 2 * n - k + 1):
            block = [
                tuple(list(p1) + [t] + (n - k) * [0])
                for p1 in IntegerListsLex(
                    length=k - 1, min_part=t, max_part=2 * n - k, max_slope=0
                )
            ]
            block.reverse()
            blocks.update({t: block})
    elif cartan_family == "E":
        raise NotImplementedError()
    elif cartan_family == "F":
        raise NotImplementedError()
    elif cartan_family == "G":
        raise NotImplementedError()
    for block_index, block in blocks.items():
        stock = []
        for coefficients in block:
            if cartan_family == "A":
                highest_weight = tuple(
                    [
                        coefficients[i] - coefficients[i + 1]
                        for i in range(len(coefficients) - 1)
                    ]
                )
                bdl = bundle.BundleBWB.from_tuple(base_space, highest_weight, "fw")
                description = str(bdl)
            elif cartan_family == "B" or cartan_family == "C" or cartan_family == "D":
                highest_weight = coefficients
                bdl = bundle.BundleBWB.from_tuple(base_space, highest_weight, "ambt")
                if len(stock) == 0:
                    description = str(bdl)
                else:
                    description = "Right mutation of {} through {}.".format(
                        str(bdl), ",".join(stock)
                    )
            elif cartan_family == "E" or cartan_family == "F" or cartan_family == "G":
                raise NotImplementedError()
            yield block_index, coefficients, description
            stock += [str(bdl)]


def SpinorSubcollection(n: int) -> LefschetzCollection:
    assert n in ZZ, "The input for `n` needs to be an integer."
    assert 3 < n, "The integer `n` needs to be greater than 3."
    X = variety.OGr(3, 2 * n + 1)
    rows = []
    for d in range(n - 1):
        if d == 0:
            bdl = X.S()
            row_length = 2 * n - 3
        elif 1 <= d and d <= n - 3:
            bdl = X.S() * X.U().dual().sym(d) + X.S() * X.U().dual().sym(d - 1)
            row_length = 2 * n - 3
        elif d == n - 2:
            bdl = X.S() * X.U().dual().sym(n - 2) + X.S() * X.U().dual().sym(n - 3)
            row_length = n - 2
        rows += [(bdl, row_length)]
    return Construct_2D_by_rows(X.O(1), rows)


def TautologicalSubcollection(n: int) -> LefschetzCollection:
    assert n in ZZ, "The input for `n` needs to be an integer."
    assert 3 < n, "The integer `n` needs to be greater than 3."
    X = variety.OGr(3, 2 * n + 1)
    weights = []
    weights += [
        tuple(list(partition) + (n - 3) * [0])
        for partition in IntegerListsLex(
            length=3,
            floor=[n - 2, 0, 0],
            ceiling=[floor(3 / 2 * (n - 3)), ceil(1 / 2 * (n - 3)), 0],
            min_slope=-n + 3,
            max_slope=0,
        )
    ]
    weights += [
        tuple(list(partition) + (n - 3) * [0])
        for partition in IntegerListsLex(
            length=3, ceiling=(3 - 1) * [n - 3] + [0], max_slope=0
        )
    ]
    weights.reverse()
    rows = []
    for weight in weights:
        bdl = bundle.BundleBWB.from_tuple(X, weight, "ambt")
        row_length = 2 * n - 3
        rows += [(bdl, row_length)]
    return Construct_2D_by_rows(X.O(1), rows)
