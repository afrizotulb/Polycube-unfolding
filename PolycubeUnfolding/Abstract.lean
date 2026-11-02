import Mathlib

/-!
# Polycube unfolding
-/

namespace PolycubeUnfolding.Abstract

/-- A point of `ℤ³`. -/
abbrev Point := Fin 3 → ℤ

/-- A prototile: a finite set of points of `ℤ³`, given as a list. -/
abbrev Protopolycube := List Point

/-- Two points are adjacent when their `ℓ¹` distance is one. -/
def Adjacent (a b : Point) : Prop :=
  ∑ i, |a i - b i| = 1

/-- `P` is (face-)connected: any two of its points are joined by a path of
adjacent points inside `P`. -/
def Connected (P : Protopolycube) : Prop :=
  ∀ p ∈ P, ∀ q ∈ P, Relation.ReflTransGen (fun a b => a ∈ P ∧ b ∈ P ∧ Adjacent a b) p q

abbrev Protocell := Point × Point

/-- A cell is located between a unit cube thas is part of the polycube, and one that is not -/
def IsProtoCell (P : Protopolycube) (C : Protocell) : Prop :=
  C.1 ∈ P ∧ C.2 ∉ P ∧ Adjacent C.1 C.2




abbrev RealPoint := Fin 3 → ℝ

def Cube (p : Point) : Set RealPoint :=
  {x | ∀ i, p i ≤ x i ∧ x i ≤ p i + 1}

/-- The solid body of a prototile: the union of the unit cubes `p + [0, 1]³`, `p ∈ P`. -/
def Polycube (P : Protopolycube) : Set RealPoint :=
  {x | ∃ p ∈ P, ∀ i, p i ≤ x i ∧ x i ≤ p i + 1}

/-- The square of a cell -/
def Cell (C : Protocell) : Set RealPoint :=
  Cube C.1 ∩ Cube C.2

/-- A n-layers flat polycube only contains points of z coordinates between 0 and n,
  and if a point (x, y, z) is in the polycube, the whole vertical segment from (x, y, 0)
  to (x, y, n) is also contained -/
def Flat (P : Set RealPoint) (n : ℝ) : Prop :=
  (∀ x ∈ P, x 2 ∈ Set.Icc 0 n) ∧
  (∀ x ∈ P, ∀ z ∈ Set.Icc 0 n,
    Function.update x 2 z ∈ P)

-- TODO : cell map thing, non-degenerate property, flat property...

end PolycubeUnfolding.Abstract
