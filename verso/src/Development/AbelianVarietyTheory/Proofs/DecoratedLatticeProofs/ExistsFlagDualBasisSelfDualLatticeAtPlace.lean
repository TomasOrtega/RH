import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WittCoreEmbeddingPreservesSupportedUnitarySubgro
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualSplitComponentIsLatticeStabilizerEq
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsIntegralBasisOfLatticeAtPlaceStable
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsFlagDualMatrix

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.IwaPlace Matrix

namespace GlobalTheory.IwaFlag

variable {D : D7} {v : Pl D}

def intGrpAt (D : D7) (v : Pl D) : AddSubgroup (AE D) where
  carrier := intAt D (· = v)
  zero_mem' := ⟨zero_mem _, by rw [RingHom.map_zero]; exact zero_mem _⟩
  add_mem' := fun ha hb => ⟨add_mem ha.1 hb.1, by rw [RingHom.map_add]; exact add_mem ha.2 hb.2⟩
  neg_mem' := fun ha => ⟨neg_mem ha.1, by rw [RingHom.map_neg]; exact neg_mem ha.2⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨Ideal.mul_mem_left _ _ hb.1, by rw [RingHom.map_mul]; exact FrameLat.mul_mem_intAE ha.2 hb.2⟩`.
-/
theorem mul_mem_intAt {a b : AE D} (ha : a ∈ intAt D (· = v)) (hb : b ∈ intAt D (· = v)) : a * b ∈ intAt D (· = v) :=
  ⟨Ideal.mul_mem_left _ _ hb.1, by rw [RingHom.map_mul]; exact FrameLat.mul_mem_intAE ha.2 hb.2⟩

/- English proof (translation)
Establish `hz : IsAlgebraic ℤ z` using `(IsFractionRing.isAlgebraic_iff ℤ ℚ D.host.E).2 (Algebra.IsAlgebraic.isAlgebraic z)`. Take `⟨y, hy, h⟩` from `hz.exists_integral_multiple`. Use `⟨y.natAbs, Int.natAbs_pos.2 hy, ?_⟩` and prove the remaining obligations. Rewrite `h` using `[zsmul_eq_mul]`. Rewrite using `[← Int.cast_natCast]`.

Break down `Int.natAbs_eq y with e | e` into its components or cases. Rewrite using `[← e]`. Conclude with `h`. Establish `e' : ((y.natAbs : ℕ) : ℤ) = -y` using `by omega`. Rewrite using `[e', Int.cast_neg, neg_mul]`.

Conclude with `h.neg`.
-/
theorem exists_nat_isIntegral (z : D.host.E) : ∃ n : ℕ, 0 < n ∧ IsIntegral ℤ ((n : D.host.E) * z) := by
  have hz : IsAlgebraic ℤ z := (IsFractionRing.isAlgebraic_iff ℤ ℚ D.host.E).2 (Algebra.IsAlgebraic.isAlgebraic z)
  obtain ⟨y, hy, h⟩ := hz.exists_integral_multiple
  refine ⟨y.natAbs, Int.natAbs_pos.2 hy, ?_⟩
  rw [zsmul_eq_mul] at h
  rw [← Int.cast_natCast]
  rcases Int.natAbs_eq y with e | e
  · rw [← e]; exact h
  · have e' : ((y.natAbs : ℕ) : ℤ) = -y := by omega
    rw [e', Int.cast_neg, neg_mul]; exact h.neg

/- English proof (translation)
Use `choose c hc hi using fun p : ι => exists_nat_isIntegral (z p)`. Use `⟨∏ p, c p, Finset.prod_pos fun p _ => hc p, fun l => ?_⟩` and prove the remaining obligations. Rewrite using `[← Finset.prod_erase_mul Finset.univ c (Finset.mem_univ l), Nat.cast_mul, mul_assoc]`. Use `IsIntegral.mul ?_ (hi l)` and prove the remaining obligations. Rewrite using `[← Int.cast_natCast]`.

Conclude with `isIntegral_algebraMap (R := ℤ)`.
-/
theorem exists_nat_isIntegral_fin {ι : Type} [Fintype ι] (z : ι → D.host.E) :
    ∃ d : ℕ, 0 < d ∧ ∀ l, IsIntegral ℤ ((d : D.host.E) * z l) := by
  classical
  choose c hc hi using fun p : ι => exists_nat_isIntegral (z p)
  refine ⟨∏ p, c p, Finset.prod_pos fun p _ => hc p, fun l => ?_⟩
  rw [← Finset.prod_erase_mul Finset.univ c (Finset.mem_univ l), Nat.cast_mul, mul_assoc]
  refine IsIntegral.mul ?_ (hi l)
  rw [← Int.cast_natCast]
  exact isIntegral_algebraMap (R := ℤ)

/- English proof (translation)
Establish `h : finPart D (incA D o) ∈ intAE D` using `AddSubgroup.subset_closure ⟨1, fun w => by rw [map_one]; exact one_mem _, ⟨o, ho⟩, rfl⟩`. Conclude with `⟨Ideal.mul_mem_right _ _ hεI.1, by rw [RingHom.map_mul]; exact FrameLat.mul_mem_intAE hεI.2 h⟩`.
-/
theorem mul_incA_mem {ε : AE D} (hεI : ε ∈ intAt D (· = v)) {o : D.host.E} (ho : IsIntegral ℤ o) :
    ε * incA D o ∈ intAt D (· = v) := by
  have h : finPart D (incA D o) ∈ intAE D :=
    AddSubgroup.subset_closure ⟨1, fun w => by rw [map_one]; exact one_mem _, ⟨o, ho⟩, rfl⟩
  exact ⟨Ideal.mul_mem_right _ _ hεI.1, by rw [RingHom.map_mul]; exact FrameLat.mul_mem_intAE hεI.2 h⟩

/- English proof (translation)
Introduce and unpack `J h1 h2 ⟨m, hm, h3⟩ ⟨N, hN, h4⟩`. Take `⟨β, β', g1, g2, g3, g4, g5⟩` from `GlobalTheory.IwaPlace.FreeAt.exists_basis D 1 v ε (J.comap (Pi.evalAddMonoidHom (fun _ : Fin 1 => AE D) 0)) ht hεε hεc hεI hε (fun y hy i => by rw [Subsingleton.elim i 0]; exact (hε _).2 (h1 _ hy)) (fun a ha y hy => h2 a ha _ hy) ⟨m, hm, fun y hy => by`. Use `h2 _ (hy 0) _ h3` as an intermediate fact. Rewrite `this` using `[mul_left_comm, mul_comm (y 0), (hε _).1 (hy 0).1]`. Conclude with `this⟩`.

Use the proof step `⟨N, hN, fun y hy i => by rw [Subsingleton.elim i 0]; exact h4 _ hy⟩`. Establish `e3 : β 0 0 * β' 0 0 = ε`. Use `congrFun (congrFun g3 0) 0` as an intermediate fact. Rewrite `this` using `[Matrix.mul_apply, Fin.sum_univ_one, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one]`. Then use the resulting hypothesis. Establish `ev : ∀ (a : AE D) (i : Fin 1), (β' *ᵥ fun _ => a) i = β' 0 0 * a` using `fun a i => by`.

Rewrite using `[Subsingleton.elim i 0, Matrix.mulVec, dotProduct, Fin.sum_univ_one]`. Use `⟨β 0 0, (g5 (fun _ => β 0 0) fun _ => g1 0 0).2 fun i => ?_, β' 0 0, (hε _).1 (g2 0 0), e3, fun a ha => ?_⟩` and prove the remaining obligations. Rewrite using `[ev, mul_comm, e3]`. Conclude with `hεI`. Use `(g5 (fun _ => a) fun _ => (hε _).2 (h1 a ha)).1 ha 0` as an intermediate fact.

Rewrite `this` using `[ev]`. Conclude with `this`.
-/
theorem princ_intGrpAt {ε : AE D} (hεε : ε * ε = ε) (hεc : cA D ε = ε) (hεI : ε ∈ intAt D (· = v))
    (hε : ∀ a, a ∈ idAt D (· = v) ↔ ε * a = a) (ht : Tame D v) : Princ ε (intGrpAt D v) := by
  rintro J h1 h2 ⟨m, hm, h3⟩ ⟨N, hN, h4⟩
  obtain ⟨β, β', g1, g2, g3, g4, g5⟩ := GlobalTheory.IwaPlace.FreeAt.exists_basis D 1 v ε (J.comap (Pi.evalAddMonoidHom (fun _ : Fin 1 => AE D) 0))
    ht hεε hεc hεI hε
    (fun y hy i => by rw [Subsingleton.elim i 0]; exact (hε _).2 (h1 _ hy))
    (fun a ha y hy => h2 a ha _ hy)
    ⟨m, hm, fun y hy => by
      have := h2 _ (hy 0) _ h3
      rw [mul_left_comm, mul_comm (y 0), (hε _).1 (hy 0).1] at this
      exact this⟩
    ⟨N, hN, fun y hy i => by rw [Subsingleton.elim i 0]; exact h4 _ hy⟩
  have e3 : β 0 0 * β' 0 0 = ε := by
    have := congrFun (congrFun g3 0) 0
    rwa [Matrix.mul_apply, Fin.sum_univ_one, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one] at this
  have ev : ∀ (a : AE D) (i : Fin 1), (β' *ᵥ fun _ => a) i = β' 0 0 * a := fun a i => by
    rw [Subsingleton.elim i 0, Matrix.mulVec, dotProduct, Fin.sum_univ_one]
  refine ⟨β 0 0, (g5 (fun _ => β 0 0) fun _ => g1 0 0).2 fun i => ?_, β' 0 0, (hε _).1 (g2 0 0), e3, fun a ha => ?_⟩
  · rw [ev, mul_comm, e3]; exact hεI
  · have := (g5 (fun _ => a) fun _ => (hε _).2 (h1 a ha)).1 ha 0
    rw [ev] at this
    exact this

/- English proof (translation)
Introduce `D S S₀ ρ d v ε hεε hεc hεI hε ht M ⟨hsupp, ⟨m, hm, hmul⟩, hdual⟩`. Take `⟨K, hK, hint⟩` from `exists_nat_isIntegral_fin (Sum.elim (fun p : Fin S.rank × Fin ρ => d.e p.1 p.2) (fun p : Fin S.rank × Fin ρ => d.e' p.1 p.2))`. Establish `hcol : ∀ z : Fin S.rank → D.host.E, (∀ l, IsIntegral ℤ ((K : D.host.E) * z l)) → (fun l => ((m * K : ℕ) : AE D) * ε * incA D (z l)) ∈ M` using `fun z hz => by`. Establish `e : (fun l => ((m * K : ℕ) : AE D) * ε * incA D (z l)) = (m : AE D) • fun l => ε * incA D ((K : D.host.E) * z l)`. Use function extensionality and compare the values at `l`.

Rewrite using `[Pi.smul_apply, smul_eq_mul, RingHom.map_mul, map_natCast, Nat.cast_mul]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `hmul _ fun l => mul_incA_mem hεI (hz l)`. Take `⟨b, h1, h2, h3, c', h4, h5⟩` from `exists_flag_dual_matrix (c := cA D) (O := intGrpAt D v) (M := M) (gA S) cA_cA hεε hεc hεI (fun a ha => (hε a).1 ha.1) (fun a ha b hb => mul_mem_intAt ha hb) (fun a ha => ⟨(hε _).2 (by rw [← hεc, ← RingHom.map_mul, (hε a).1 ha.1]), (FrameLat.cA_int_iff a).2 ha.2⟩) (princ_intGrpAt …`.

Conclude with `⟨b, h1, fun i j => (hε _).2 (h2 i j), h3, c', h4, h5⟩`.
-/
theorem exists_flag_basis : ∀ (D : D7) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (v : Pl D) (ε : AE D) (hεε : ε * ε = ε) (hεc : cA D ε = ε) (hεI : ε ∈ intAt D (· = v)) (hε : ∀ a, a ∈ idAt D (· = v) ↔ ε * a = a), Tame D v → ∀ M : AddSubgroup (Fin S.rank → AE D), IsSDAt S v M → ∃ b : Mx D ρ ρ, (∀ i j, j < i → b i j = 0) ∧ (∀ i j, b i j ∈ idAt D (· = v)) ∧ (∀ i, (fun k => (d.jX ⬝ b) k i) ∈ M) ∧ ∃ c' : Mx D S.rank ρ, (∀ i, (fun k => c' k i) ∈ M) ∧ adj c' ⬝ (gA S ⬝ (d.jX ⬝ b)) = ε • (1 : Mx D ρ ρ) := by
  intro D S S₀ ρ d v ε hεε hεc hεI hε ht M ⟨hsupp, ⟨m, hm, hmul⟩, hdual⟩
  obtain ⟨K, hK, hint⟩ := exists_nat_isIntegral_fin
    (Sum.elim (fun p : Fin S.rank × Fin ρ => d.e p.1 p.2) (fun p : Fin S.rank × Fin ρ => d.e' p.1 p.2))
  have hcol : ∀ z : Fin S.rank → D.host.E, (∀ l, IsIntegral ℤ ((K : D.host.E) * z l)) →
      (fun l => ((m * K : ℕ) : AE D) * ε * incA D (z l)) ∈ M := fun z hz => by
    have e : (fun l => ((m * K : ℕ) : AE D) * ε * incA D (z l)) =
        (m : AE D) • fun l => ε * incA D ((K : D.host.E) * z l) := by
      funext l
      rw [Pi.smul_apply, smul_eq_mul, RingHom.map_mul, map_natCast, Nat.cast_mul]
      ring
    rw [e]
    exact hmul _ fun l => mul_incA_mem hεI (hz l)
  obtain ⟨b, h1, h2, h3, c', h4, h5⟩ := exists_flag_dual_matrix (c := cA D) (O := intGrpAt D v) (M := M) (gA S)
    cA_cA hεε hεc hεI (fun a ha => (hε a).1 ha.1) (fun a ha b hb => mul_mem_intAt ha hb)
    (fun a ha => ⟨(hε _).2 (by rw [← hεc, ← RingHom.map_mul, (hε a).1 ha.1]), (FrameLat.cA_int_iff a).2 ha.2⟩)
    (princ_intGrpAt hεε hεc hεI hε ht) (fun y hy i => (hε _).1 (hsupp y hy i))
    (fun y hy => hdual y fun i => (hε _).2 (hy i)) d.jX d.jY d.gram_YX (m * K) (Nat.mul_pos hm hK)
    (fun k => hcol (fun l => d.e l k) fun l => hint (Sum.inl (l, k)))
    (fun k => hcol (fun l => d.e' l k) fun l => hint (Sum.inr (l, k)))
  exact ⟨b, h1, fun i j => (hε _).2 (h2 i j), h3, c', h4, h5⟩

end GlobalTheory.IwaFlag

end
