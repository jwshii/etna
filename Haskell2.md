
0. (TODO: This step is out of date because I removed the template. Just copy-and-paste an old one for now.)

    To add a new workload `?b`, run `stack new ?b template.hsfiles` in `bench-suite/Haskell`. This will provide the boilerplate files, though `app/Main.hs` will need to be instantiated manually.

1. `src/Impl.hs` should contain the implementation. Here is an example of the mutant syntax: 

   ```haskell
    delete :: Int -> Tree Int -> Tree Int
    delete x Leaf = Leaf
    delete x (Branch l x' r)
      {-! -}
      | x < x' = Branch (delete x l) x' r
      | x > x' = Branch l x' (delete x r)
      | otherwise = join l r
      {-!! delete_reverse_check -}
      {-!
      | x > x' = Branch (delete x l) x' r
      | x < x' = Branch l x' (delete x r)
      | otherwise = join l r
      -}
   ```

   The base implementation is provided directly under an empty `{-! -}`. The mutant names are within `{-!! -}` and the mutant implementations are commented out inside `{-! -}`.

   The parsing currently makes a lot of assumptions. In particular, the commented out mutant code should, if the comment brackets are removed, be indented correctly. The autoformatter in VSCode most likely will want to change the indentation — save without formatting instead. (Yes, this should be fixed.)


2. `src/Spec.hs` should contain the specification.
    (Unlike `Impl`, which must be named that, this is just by convention.)

    You must use the provided `Task` type and gather arguments in a tuple. For example, 

    ```haskell
    prop_InsertPost :: Task (BST, Key, Key, Val)
    prop_InsertPost (t, k, k', v) =
      isBST t
        --> find k' (insert k v t)
        == if k == k' then Just v else find k' t
    ```

    Notice the use of the `-->` combinator for preconditions.

4. (TODO: The paper now uses "strategy" instead of "method." Need to update throughout.)

    To add a new method `?M`, create a file `src/Method/?M.hs`.

    Inside `common/bench-lib`, there are various things to help. Consider these examples in `BST/src/Method`. For QuickCheck methodologies, 

    - An example using rejection sampling can be found in `Quick.hs`.

    - An example for a correct-by-construction method can be found in `Correct.hs`.

    Examples outside the QuickCheck framework can be found in `Small.hs` for `SmallCheck` and `Lean.hs` for `LeanCheck`.
