import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LocalPublishedTheorems

noncomputable section

namespace UpperTheory.V.Loc

open ReciprocityTheory.Gal

def coSub {G A V : Type} [Group G] [CommRing A] [AddCommGroup V] [Module A V] (χ : G →* Aˣ)
    (ρ : Representation A G V) : Submodule A V :=
  Submodule.span A {y | ∃ g x, y = ρ g x - ((χ g : Aˣ) : A) • x}

def lSub (l : ℕ) [Fact l.Prime] (X : Type) [AddCommGroup X] [Module ℤ_[l] X] (m : ℕ) : Submodule ℤ_[l] X :=
  LinearMap.range (((l : ℤ_[l]) ^ m) • (LinearMap.id : X →ₗ[ℤ_[l]] X))

/- English proof (translation)
Simplify using `only [lSub, LinearMap.mem_range, LinearMap.smul_apply, LinearMap.id_apply]`.
-/
theorem mem_lSub {l : ℕ} [Fact l.Prime] {X : Type} [AddCommGroup X] [Module ℤ_[l] X] {m : ℕ} {x : X} :
    x ∈ lSub l X m ↔ ∃ y, (l : ℤ_[l]) ^ m • y = x := by
  simp only [lSub, LinearMap.mem_range, LinearMap.smul_apply, LinearMap.id_apply]

def redRep {l : ℕ} [Fact l.Prime] {G X : Type} [Group G] [AddCommGroup X] [Module ℤ_[l] X]
    (ρ : Representation ℤ_[l] G X) (m : ℕ) : Representation ℤ_[l] G (X ⧸ lSub l X m) :=
  ρ.quotient (lSub l X m) fun g _ hx => by
    obtain ⟨y, rfl⟩ := mem_lSub.1 hx
    exact mem_lSub.2 ⟨ρ g y, (map_smul _ _ _).symm⟩

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem redRep_mk {l : ℕ} [Fact l.Prime] {G X : Type} [Group G] [AddCommGroup X] [Module ℤ_[l] X]
    (ρ : Representation ℤ_[l] G X) (m : ℕ) (g : G) (x : X) :
    redRep ρ m g (Submodule.Quotient.mk x) = Submodule.Quotient.mk (ρ g x) := rfl

/- English proof (translation)
Rewrite using `[mem_lSub]`. Establish `key : ∀ a : ℤ_[l], PadicInt.toZModPow m a = 0 ↔ (l : ℤ_[l]) ^ m ∣ a`. Introduce `a`. Rewrite using `[← RingHom.mem_ker, PadicInt.ker_toZModPow, Ideal.mem_span_singleton]`. Simplify using `only [key]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, rfl⟩ i`. Conclude with `⟨y i, rfl⟩`. Introduce `h choose y hy using h`. Conclude with `⟨y, funext fun i => by simp [Pi.smul_apply, smul_eq_mul, hy i]⟩`.
-/
theorem mem_lSub_pi {l : ℕ} [Fact l.Prime] {n m : ℕ} {x : Fin n → ℤ_[l]} :
    x ∈ lSub l (Fin n → ℤ_[l]) m ↔ ∀ i, PadicInt.toZModPow m (x i) = 0 := by
  rw [mem_lSub]
  have key : ∀ a : ℤ_[l], PadicInt.toZModPow m a = 0 ↔ (l : ℤ_[l]) ^ m ∣ a := by
    intro a
    rw [← RingHom.mem_ker, PadicInt.ker_toZModPow, Ideal.mem_span_singleton]
  simp only [key]
  constructor
  · rintro ⟨y, rfl⟩ i
    exact ⟨y i, rfl⟩
  · intro h
    choose y hy using h
    exact ⟨y, funext fun i => by simp [Pi.smul_apply, smul_eq_mul, hy i]⟩

/- English proof (translation)
Establish `hset : ((lSub l (Fin n → ℤ_[l]) m : Submodule ℤ_[l] (Fin n → ℤ_[l])) : Set (Fin n → ℤ_[l])) = ⋂ i, (fun x : Fin n → ℤ_[l] => x i) ⁻¹' Metric.closedBall (0 : ℤ_[l]) ((l : ℝ) ^ (-(m : ℤ)))`. Use extensionality with `x`. Simplify using `only [SetLike.mem_coe, mem_lSub_pi, Set.mem_iInter, Set.mem_preimage, mem_closedBall_zero_iff]`. Use `forall_congr' fun i => ?_` and prove the remaining obligations. Rewrite using `[← RingHom.mem_ker, PadicInt.ker_toZModPow, ← PadicInt.norm_le_pow_iff_mem_span_pow]`.

Rewrite using `[hset]`. Conclude with `isOpen_iInter_of_finite fun i => (IsUltrametricDist.isOpen_closedBall _ (zpow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero))).preimage (continuous_apply i)`.
-/
theorem isOpen_lSub_pi (l : ℕ) [Fact l.Prime] (n m : ℕ) :
    IsOpen ((lSub l (Fin n → ℤ_[l]) m : Submodule ℤ_[l] (Fin n → ℤ_[l])) : Set (Fin n → ℤ_[l])) := by
  have hset : ((lSub l (Fin n → ℤ_[l]) m : Submodule ℤ_[l] (Fin n → ℤ_[l])) : Set (Fin n → ℤ_[l])) =
      ⋂ i, (fun x : Fin n → ℤ_[l] => x i) ⁻¹' Metric.closedBall (0 : ℤ_[l]) ((l : ℝ) ^ (-(m : ℤ))) := by
    ext x
    simp only [SetLike.mem_coe, mem_lSub_pi, Set.mem_iInter, Set.mem_preimage, mem_closedBall_zero_iff]
    refine forall_congr' fun i => ?_
    rw [← RingHom.mem_ker, PadicInt.ker_toZModPow, ← PadicInt.norm_le_pow_iff_mem_span_pow]
  rw [hset]
  exact isOpen_iInter_of_finite fun i =>
    (IsUltrametricDist.isOpen_closedBall _
      (zpow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero))).preimage (continuous_apply i)

instance discrete_quot_lSub (l : ℕ) [Fact l.Prime] (n m : ℕ) :
    DiscreteTopology ((Fin n → ℤ_[l]) ⧸ lSub l (Fin n → ℤ_[l]) m) :=
  QuotientAddGroup.discreteTopology (N := (lSub l (Fin n → ℤ_[l]) m).toAddSubgroup) (isOpen_lSub_pi l n m)

/- English proof (translation)
Set `f : (Fin n → ℤ_[l]) →+ (Fin n → ZMod (l ^ m))` to `AddMonoidHom.compLeft (PadicInt.toZModPow m : ℤ_[l] →+* ZMod (l ^ m)).toAddMonoidHom (Fin n)`. Establish `hf : Function.Surjective f`. Introduce `z`. Use `choose k hk using fun i => ZMod.intCast_surjective (z i)`. Conclude with `⟨fun i => (k i : ℤ_[l]), funext fun i => by simp [f, hk i]⟩`.

Establish `hk : f.ker = (lSub l (Fin n → ℤ_[l]) m).toAddSubgroup`. Use extensionality with `x`. Simplify using `[f, mem_lSub_pi, funext_iff]`. Establish `e : ((Fin n → ℤ_[l]) ⧸ lSub l (Fin n → ℤ_[l]) m) ≃ (Fin n → ZMod (l ^ m))` using `((QuotientAddGroup.quotientAddEquivOfEq hk.symm).trans (QuotientAddGroup.quotientKerEquivOfSurjective f hf)).toEquiv`. Rewrite using `[Nat.card_congr e]`.

Simplify using `[Nat.card_fun, pow_mul]`.
-/
theorem card_quot_lSub (l : ℕ) [Fact l.Prime] (n m : ℕ) :
    Nat.card ((Fin n → ℤ_[l]) ⧸ lSub l (Fin n → ℤ_[l]) m) = l ^ (m * n) := by
  let f : (Fin n → ℤ_[l]) →+ (Fin n → ZMod (l ^ m)) :=
    AddMonoidHom.compLeft (PadicInt.toZModPow m : ℤ_[l] →+* ZMod (l ^ m)).toAddMonoidHom (Fin n)
  have hf : Function.Surjective f := by
    intro z
    choose k hk using fun i => ZMod.intCast_surjective (z i)
    exact ⟨fun i => (k i : ℤ_[l]), funext fun i => by simp [f, hk i]⟩
  have hk : f.ker = (lSub l (Fin n → ℤ_[l]) m).toAddSubgroup := by
    ext x
    simp [f, mem_lSub_pi, funext_iff]
  have e : ((Fin n → ℤ_[l]) ⧸ lSub l (Fin n → ℤ_[l]) m) ≃ (Fin n → ZMod (l ^ m)) :=
    ((QuotientAddGroup.quotientAddEquivOfEq hk.symm).trans
      (QuotientAddGroup.quotientKerEquivOfSurjective f hf)).toEquiv
  rw [Nat.card_congr e]
  simp [Nat.card_fun, pow_mul]

instance finite_quot_lSub (l : ℕ) [Fact l.Prime] (n m : ℕ) :
    Finite ((Fin n → ℤ_[l]) ⧸ lSub l (Fin n → ℤ_[l]) m) :=
  Nat.finite_of_card_ne_zero (by rw [card_quot_lSub]; exact pow_ne_zero _ (Fact.out : l.Prime).ne_zero)

/- English proof (translation)
Unfold `ReciprocityTheory.Gal.ContAction at h ⊢`. Rewrite using `[← (IsOpenQuotientMap.id.prodMap (lSub l (Fin n → ℤ_[l]) m).isOpenQuotientMap_mkQ).continuous_comp_iff]`. Use `((lSub l (Fin n → ℤ_[l]) m).continuous_mkQ.comp h).congr ?_` and prove the remaining obligations. Introduce `p`. Conclude with `(redRep_mk ρ m p.1 p.2).symm`.
-/
theorem contAction_redRep {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] {n : ℕ}
    {ρ : Representation ℤ_[l] G (Fin n → ℤ_[l])} (h : ContAction ρ) (m : ℕ) : ContAction (redRep ρ m) := by
  unfold ReciprocityTheory.Gal.ContAction at h ⊢
  rw [← (IsOpenQuotientMap.id.prodMap (lSub l (Fin n → ℤ_[l]) m).isOpenQuotientMap_mkQ).continuous_comp_iff]
  refine ((lSub l (Fin n → ℤ_[l]) m).continuous_mkQ.comp h).congr ?_
  intro p
  exact (redRep_mk ρ m p.1 p.2).symm

def FinLevel (l : ℕ) [Fact l.Prime] (G : Type) [Group G] [TopologicalSpace G] (χ : G →* ℤ_[l]ˣ) (d : ℕ) : Prop :=
  ∀ (M : Type) [AddCommGroup M] [Module ℤ_[l] M] [Finite M] [TopologicalSpace M] [DiscreteTopology M]
    (ρ : Representation ℤ_[l] G M), ContAction ρ →
    Finite (H1 ρ) ∧ Finite (H2 ρ) ∧ (∀ n, 3 ≤ n → Subsingleton (Hn ρ n)) ∧
      Nat.card (H1 ρ) = Nat.card (H0 ρ) * Nat.card (H2 ρ) * Nat.card M ^ d ∧
      Nat.card (H2 ρ) = Nat.card (M ⧸ coSub χ ρ)

def FinLevelMod (l : ℕ) [Fact l.Prime] (G : Type) [Group G] [TopologicalSpace G] (χ : G →* ℤ_[l]ˣ) (d : ℕ) :
    Prop :=
  ∀ (r : ℕ), 0 < r → ∀ (M : Type) [AddCommGroup M] [Module (ZMod (l ^ r)) M] [Finite M] [TopologicalSpace M]
    [DiscreteTopology M] (ρ : Representation (ZMod (l ^ r)) G M), ContAction ρ →
    Finite (H1 ρ) ∧ Finite (H2 ρ) ∧ (∀ n, 3 ≤ n → Subsingleton (Hn ρ n)) ∧
      Nat.card (H1 ρ) = Nat.card (H0 ρ) * Nat.card (H2 ρ) * Nat.card M ^ d ∧
      Nat.card (H2 ρ) = Nat.card (H0dual
        ((Units.map (PadicInt.toZModPow r : ℤ_[l] →+* ZMod (l ^ r)).toMonoidHom).comp χ) ρ)

def Grows (l : ℕ) (a : ℕ → ℕ) (s : ℕ) : Prop := ∃ C : ℕ, ∀ m, 0 < m → l ^ (m * s) ≤ a m ∧ a m ≤ l ^ (m * s + C)

end UpperTheory.V.Loc
