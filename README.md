# free-alternative-other

The other free `Alternative`.

There is the implementation of the free `Alternative` in `free`.

- free --- [Control.Alternative.Free](https://hackage.haskell.org/package/free-5.2/docs/Control-Alternative-Free.html)

But, strictly speaking, what we call `Alternative` is not one type class,
but multiple "virtual" type classes sharing the same methods `empty, (<|>)`.

The above package provides the free `Alternative` for *one* such "virtual" type class.
This package provides for another.

## Multiple Alternatives

While there are no explicitly stated laws, instances of `Alternative` have always been satisfying these laws.

```
-- (mempty, <|>) forms a Monoid
mempty <|> x = x
x <|> mempty = x
x <|> (y <|> z) = (x <|> y) <|> z
```

Additionaly, most of the times, the following _left zero_ law is satisfied, and
implicitly assumed.

```
-- left zero
empty <*> x = empty
```

But there are mainly two additional expected laws for `Alternative f`, and
existing instances often satisfy *only one of them* (and none of them sometimes.)

1. _left distribution_

   ```
   (x <|> y) <*> z = (x <*> z) <|> (y <*> z)
   ```
   
   For instances satisfying _left distribution_ law, the `(<|>)` operator
   means *multiple choices* among possible actions. For them, _left distribution_ law
   states that "choose `x` or `y`, then perform `z`" is equivalent to
   "choose between `x`-then-`z` or `y`-then-`z`."

   **Notable instances:** `Maybe`, `[]`, parsers

2. _left catch_

   ```
   pure x <|> z = pure x
   ```

   For instances satisfying _left catch_ law, the `(<|>)` operator
   means *recovery from failures of the left operand*. For them, _left catch_ law
   states that `pure x` must be a complete success and nothing changes
   by adding recovery plan `z` to it.

   **Notable instances:** `Maybe`, `Either`, `IO`

The existing implementation from `free` is the former: the free `Alternative` with _left distribution_,
and this package provides the latter: the free `Alternative` with _left catch_.