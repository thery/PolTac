[![Build Status](https://travis-ci.com/thery/PolTac.svg?branch=master)](https://travis-ci.com/thery/PolTac)

# PolTac

A set of tactics to deal with inequalities in Coq over N, Z and R:

- `pols`: simplification
- `polf`: factorization
- `polr`: replacement

inspired from <https://hal.inria.fr/inria-00070394>

To build:

```shell
make all
```

To use it:

```coq
Require Import PolTac.
```

## Examples

See `Nex.v`, `Zex.v` and `Rex.v`.

### Demo: a running example (`polr_test2` in `Rex.v`)

```coq
1 subgoal
x : R
y : R
z : R
t : R
u : R
H : t < 0
H1 : y = u
H2 : x + z < y
______________________________________(1/1)
2 * y * t < x * t + t * u + z * t
```

We use `polf` to remove `t` from the left and the right side of the inequality since `t` is negative it changes the direction of the inequality.

```coq
polf.

1 subgoal

....
H1 : y = u
....
______________________________________(1/1)
x + u + z < 2 * y
```

We use `polr` to replace `u` by `y` in the goal.


```coq
polr H1; auto with real.

1 subgoal

....
H2 : x + z < y
....
______________________________________(1/1)
x + y + z < 2 * y
```

We use `polr` to bound `x + y + z` using `H2`.

```coq
polr H2.

2 subgoals
...
______________________________________(1/2)
x + y + z < y + y

...
______________________________________(2/2)
y + y <= 2 * y
```

We use pols to simply by y on both sides.

```coq
pols.

2 subgoals
...
______________________________________(1/2)
x + z < y

...
______________________________________(2/2)
y + y <= 2 * y
```

This exactly `H2`.

```coq
exact H2.

1 subgoal

...
______________________________________(1/1)
y + y <= 2 * y
```

We use pols to simply by y on both sides.

```coq
1 subgoal
...
______________________________________(1/1)
0 <= 0
```

----

Laurent.Thery@sophia.inria.fr
