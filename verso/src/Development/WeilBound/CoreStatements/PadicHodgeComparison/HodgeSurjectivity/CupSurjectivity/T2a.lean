import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.CupSurjectivity.CupK

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.LogCris

namespace CrystallineSemistableComparison.Onto

open Pb HT

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

/- English proof (translation)
Establish `hfin : ∀ a n, FiniteDimensional K (Hdg M.q a n)` using `fun a n => (P.fin M hM a n).1`. Establish `assoc : ∀ {a1 a2 i1 j1 a23 jk : ℕ} (h12 : a1 + a2 = A) (g12 : i1 + j1 = t) (h3 : a2 + a' = a23) (g3 : j1 + n = jk) (u : Hdg M.q a1 i1) (v : Hdg M.q a2 j1), th hC S sl ψ (S.pl₂ a' n x) (cupH S.P.q h12 g12 (S.pl₁ a1 i1 u) (S.pl₂ a2 j1 v)) = ψ (sl (cupH S.P.q (by omega : a1 + a23 = …`. Introduce `a1 a2 i1 j1 a23 jk h12 g12 h3 g3 u v`. Simplify using `only [th, LinearMap.comp_apply, LinearMap.flip_apply, cupL_apply]`. Rewrite using `[(hC K S.P.gen S.P.q).2.1 h12 (by omega) h3 (by omega) g12 (by omega) g3 (by omega), ← (hC K M.gen M.q).2.2.2.2.1 S.P.gen S.P.q (Model.genMap S.p₂ S.h₂) (Model.genMap_q S.p₂ S.h₂) h3 g3 v x]`.

Use `(cupK P hM S X Y Z hZ (fun a => Module.finBasis K (Hdg M.q a t)) (fun a => Module.finBasis K (Hdg M.q a 0)) A _).trans ?_` and prove the remaining obligations. Rewrite using `[Fintype.sum_eq_single (⟨(A, 0), by simp⟩ : (Finset.HasAntidiagonal.antidiagonal A : Finset (ℕ × ℕ)))]`. Use `swap`. Introduce and unpack `⟨⟨p1, p2⟩, hm⟩ hp`. Establish `hm' : p1 + p2 = A` using `Finset.HasAntidiagonal.mem_antidiagonal.1 hm`.

Establish `h2 : 0 < p2`. Break down `Nat.eq_zero_or_pos p2 with h0 | h0` into its components or cases. Conclude with `absurd (by simp only [Subtype.mk.injEq, Prod.mk.injEq]; exact ⟨by omega, h0⟩) hp`. Conclude with `h0`. Simplify using `only`.

Establish `hsub : Subsingleton (Hdg M.q p2 0)` using `(P.fin M hM p2 0).2 h2`. Use `Finset.sum_eq_zero fun s _ => Finset.sum_eq_zero fun s' _ => ?_` and prove the remaining obligations. Conclude with `absurd (Subsingleton.elim _ _) ((Module.finBasis K (Hdg M.q p2 0)).ne_zero s')`. Simplify using `only`. Distinguish the cases in `hAα : A = α`.

Substitute `hAα` using the available equality. Take `rfl : β = a'` from `by omega`. Establish `hG : ∀ v : Hdg M.q 0 0, Gx hC x ψ v = ψ (cupH M.q (Nat.zero_add β) (Nat.zero_add n) v x)`. Introduce `v`. Unfold `Gx`.

Rewrite using `[dif_pos (Nat.zero_add β)]`. Simplify using `only [LinearMap.comp_apply, LinearMap.flip_apply, cupL_apply]`. Establish `hterm : ∀ (s : Fin (Module.finrank K (Hdg M.q A t))) (s' : Fin (Module.finrank K (Hdg M.q 0 0))), th hC S sl ψ (S.pl₂ β n x) (cupH S.P.q (Nat.add_zero A) rfl (S.pl₁ A t (Module.finBasis K (Hdg M.q A t) s)) (S.pl₂ 0 0 (Module.finBasis K (Hdg M.q 0 0) s'))) = φ' (Module.finBasis K …`. Introduce `s s'`. Rewrite using `[assoc (Nat.add_zero A) rfl (Nat.zero_add β) (Nat.zero_add n), hsl.1, map_smul, smul_eq_mul, hG]`.

Rewrite using `[← bsum (kC K) (P.h M A t (M.toV t X)) (fun k φ => P.lin' M A t k _ φ) (Module.finBasis K (Hdg M.q A t)) φ', ← bsum (kC K) (P.h M 0 0 (M.toV 0 Y)) (fun k φ => P.lin' M 0 0 k _ φ) (Module.finBasis K (Hdg M.q 0 0)) (Gx hC x ψ), Finset.sum_mul_sum]`. Use `Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun s' _ => ?_` and prove the remaining obligations. Use `erw [hterm s s']`. Rewrite using `[map_mul]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hG0 : Gx hC x ψ = 0`. Unfold `Gx`. Rewrite using `[dif_neg (show ¬ (0 + a' = β) by omega)]`. Simplify using `only [hG0, map_zero, mul_zero]`. Use `Finset.sum_eq_zero fun s _ => Finset.sum_eq_zero fun s' _ => ?_` and prove the remaining obligations.

Use `erw [assoc (i1 := t) (j1 := 0) (Nat.add_zero A) (Nat.add_zero t) rfl rfl, hsl.2 A t (0 + a') (0 + n) _ _ (fun h => hAα (congrArg Prod.fst h))]`. Simplify using `only [map_zero, mul_zero]`.
-/
theorem t2z (hC : CupLaws) (P : HTPre l K) {M : Model l K} (hM : M.Sm) {D : ℕ} (S : Sq M D) {a' n : ℕ} (x : Hdg M.q a' n)
    {α β A t : ℕ} (hA : α + β = A + a') (φ' : Module.Dual K (Hdg M.q α t)) (ψ : Module.Dual K (Hdg M.q β n))
    (sl : Hdg S.P.q (A + a') (t + n) →ₗ[K] Hdg M.q β n) (hsl : IsSl S hA φ' sl)
    (X : M.T t) (Y : M.T 0) (Z : S.P.T (t + 0))
    (hZ : S.P.CupT (Model.pullT S.p₁ S.h₁ t X) (Model.pullT S.p₂ S.h₂ 0 Y) Z) :
    P.h S.P A t (S.P.toV t Z) (th hC S sl ψ (S.pl₂ a' n x)) =
      P.h M α t (M.toV t X) φ' * P.h M 0 0 (M.toV 0 Y) (Gx hC x ψ) := by
  classical
  have hfin : ∀ a n, FiniteDimensional K (Hdg M.q a n) := fun a n => (P.fin M hM a n).1
  have assoc : ∀ {a1 a2 i1 j1 a23 jk : ℕ} (h12 : a1 + a2 = A) (g12 : i1 + j1 = t) (h3 : a2 + a' = a23)
      (g3 : j1 + n = jk) (u : Hdg M.q a1 i1) (v : Hdg M.q a2 j1),
      th hC S sl ψ (S.pl₂ a' n x) (cupH S.P.q h12 g12 (S.pl₁ a1 i1 u) (S.pl₂ a2 j1 v)) =
        ψ (sl (cupH S.P.q (by omega : a1 + a23 = A + a') (by omega : i1 + jk = t + n) (S.pl₁ a1 i1 u)
          (S.pl₂ a23 jk (cupH M.q h3 g3 v x)))) := by
    intro a1 a2 i1 j1 a23 jk h12 g12 h3 g3 u v
    simp only [th, LinearMap.comp_apply, LinearMap.flip_apply, cupL_apply]
    rw [(hC K S.P.gen S.P.q).2.1 h12 (by omega) h3 (by omega) g12 (by omega) g3 (by omega),
      ← (hC K M.gen M.q).2.2.2.2.1 S.P.gen S.P.q (Model.genMap S.p₂ S.h₂) (Model.genMap_q S.p₂ S.h₂) h3 g3 v x]
  refine (cupK P hM S X Y Z hZ (fun a => Module.finBasis K (Hdg M.q a t))
    (fun a => Module.finBasis K (Hdg M.q a 0)) A _).trans ?_
  rw [Fintype.sum_eq_single (⟨(A, 0), by simp⟩ : (Finset.HasAntidiagonal.antidiagonal A : Finset (ℕ × ℕ)))]
  swap
  · rintro ⟨⟨p1, p2⟩, hm⟩ hp
    have hm' : p1 + p2 = A := Finset.HasAntidiagonal.mem_antidiagonal.1 hm
    have h2 : 0 < p2 := by
      rcases Nat.eq_zero_or_pos p2 with h0 | h0
      · exact absurd (by simp only [Subtype.mk.injEq, Prod.mk.injEq]; exact ⟨by omega, h0⟩) hp
      · exact h0
    dsimp only
    have hsub : Subsingleton (Hdg M.q p2 0) := (P.fin M hM p2 0).2 h2
    refine Finset.sum_eq_zero fun s _ => Finset.sum_eq_zero fun s' _ => ?_
    exact absurd (Subsingleton.elim _ _) ((Module.finBasis K (Hdg M.q p2 0)).ne_zero s')
  dsimp only
  by_cases hAα : A = α
  · subst hAα
    obtain rfl : β = a' := by omega
    have hG : ∀ v : Hdg M.q 0 0, Gx hC x ψ v = ψ (cupH M.q (Nat.zero_add β) (Nat.zero_add n) v x) := by
      intro v
      unfold Gx
      rw [dif_pos (Nat.zero_add β)]
      simp only [LinearMap.comp_apply, LinearMap.flip_apply, cupL_apply]
    have hterm : ∀ (s : Fin (Module.finrank K (Hdg M.q A t))) (s' : Fin (Module.finrank K (Hdg M.q 0 0))),
        th hC S sl ψ (S.pl₂ β n x) (cupH S.P.q (Nat.add_zero A) rfl (S.pl₁ A t (Module.finBasis K (Hdg M.q A t) s))
          (S.pl₂ 0 0 (Module.finBasis K (Hdg M.q 0 0) s'))) =
        φ' (Module.finBasis K (Hdg M.q A t) s) * Gx hC x ψ (Module.finBasis K (Hdg M.q 0 0) s') := by
      intro s s'
      rw [assoc (Nat.add_zero A) rfl (Nat.zero_add β) (Nat.zero_add n), hsl.1, map_smul, smul_eq_mul, hG]
    rw [← bsum (kC K) (P.h M A t (M.toV t X)) (fun k φ => P.lin' M A t k _ φ) (Module.finBasis K (Hdg M.q A t)) φ',
      ← bsum (kC K) (P.h M 0 0 (M.toV 0 Y)) (fun k φ => P.lin' M 0 0 k _ φ) (Module.finBasis K (Hdg M.q 0 0)) (Gx hC x ψ),
      Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun s' _ => ?_
    erw [hterm s s']
    rw [map_mul]
    ring
  · have hG0 : Gx hC x ψ = 0 := by
      unfold Gx
      rw [dif_neg (show ¬ (0 + a' = β) by omega)]
    simp only [hG0, map_zero, mul_zero]
    refine Finset.sum_eq_zero fun s _ => Finset.sum_eq_zero fun s' _ => ?_
    erw [assoc (i1 := t) (j1 := 0) (Nat.add_zero A) (Nat.add_zero t) rfl rfl,
      hsl.2 A t (0 + a') (0 + n) _ _ (fun h => hAα (congrArg Prod.fst h))]
    simp only [map_zero, mul_zero]

/- English proof (translation)
Establish `hfin : ∀ a n, FiniteDimensional K (Hdg M.q a n)` using `fun a n => (P.fin M hM a n).1`. Substitute `hij` using the available equality. Establish `assoc : ∀ {a1 a2 i1 j1 a23 jk : ℕ} (h12 : a1 + a2 = A) (g12 : i1 + j1 = (i + j)) (h3 : a2 + a' = a23) (g3 : j1 + n = jk) (u : Hdg M.q a1 i1) (v : Hdg M.q a2 j1), th hC S sl ψ (S.pl₂ a' n x) (cupH S.P.q h12 g12 (S.pl₁ a1 i1 u) (S.pl₂ a2 j1 v)) = ψ (sl (cupH S.P.q (by omega : a1 + …`. Introduce `a1 a2 i1 j1 a23 jk h12 g12 h3 g3 u v`. Simplify using `only [th, LinearMap.comp_apply, LinearMap.flip_apply, cupL_apply]`.

Rewrite using `[(hC K S.P.gen S.P.q).2.1 h12 (by omega) h3 (by omega) g12 (by omega) g3 (by omega), ← (hC K M.gen M.q).2.2.2.2.1 S.P.gen S.P.q (Model.genMap S.p₂ S.h₂) (Model.genMap_q S.p₂ S.h₂) h3 g3 v x]`. Use `(cupK P hM S X Y Z hZ (fun a => Module.finBasis K (Hdg M.q a i)) (fun a => Module.finBasis K (Hdg M.q a j)) A _).trans ?_` and prove the remaining obligations. Use `Finset.sum_eq_zero fun p _ => Finset.sum_eq_zero fun s _ => Finset.sum_eq_zero fun s' _ => ?_` and prove the remaining obligations. Establish `hm : p.1.1 + p.1.2 = A` using `Finset.HasAntidiagonal.mem_antidiagonal.1 p.2`. Rewrite using `[assoc hm rfl rfl rfl, hsl.2 p.1.1 i (p.1.2 + a') (j + n) (by omega) (by omega) (fun h => hj (by have := congrArg Prod.snd h; dsimp only at this; omega))]`.

Simplify using `only [map_zero, mul_zero]`.
-/
theorem t2a (hC : CupLaws) (P : HTPre l K) {M : Model l K} (hM : M.Sm) {D : ℕ} (S : Sq M D) {a' n : ℕ} (x : Hdg M.q a' n)
    {α β A t : ℕ} (hA : α + β = A + a') (φ' : Module.Dual K (Hdg M.q α t)) (ψ : Module.Dual K (Hdg M.q β n))
    (sl : Hdg S.P.q (A + a') (t + n) →ₗ[K] Hdg M.q β n) (hsl : IsSl S hA φ' sl)
    {i j : ℕ} (X : M.T i) (Y : M.T j) (Z : S.P.T (i + j))
    (hZ : S.P.CupT (Model.pullT S.p₁ S.h₁ i X) (Model.pullT S.p₂ S.h₂ j Y) Z) (hij : i + j = t) (hj : j ≠ 0) :
    P.h S.P A t (S.P.toV t (castT hij Z)) (th hC S sl ψ (S.pl₂ a' n x)) = 0 := by
  classical
  have hfin : ∀ a n, FiniteDimensional K (Hdg M.q a n) := fun a n => (P.fin M hM a n).1
  subst hij
  have assoc : ∀ {a1 a2 i1 j1 a23 jk : ℕ} (h12 : a1 + a2 = A) (g12 : i1 + j1 = (i + j)) (h3 : a2 + a' = a23)
      (g3 : j1 + n = jk) (u : Hdg M.q a1 i1) (v : Hdg M.q a2 j1),
      th hC S sl ψ (S.pl₂ a' n x) (cupH S.P.q h12 g12 (S.pl₁ a1 i1 u) (S.pl₂ a2 j1 v)) =
        ψ (sl (cupH S.P.q (by omega : a1 + a23 = A + a') (by omega : i1 + jk = (i + j) + n) (S.pl₁ a1 i1 u)
          (S.pl₂ a23 jk (cupH M.q h3 g3 v x)))) := by
    intro a1 a2 i1 j1 a23 jk h12 g12 h3 g3 u v
    simp only [th, LinearMap.comp_apply, LinearMap.flip_apply, cupL_apply]
    rw [(hC K S.P.gen S.P.q).2.1 h12 (by omega) h3 (by omega) g12 (by omega) g3 (by omega),
      ← (hC K M.gen M.q).2.2.2.2.1 S.P.gen S.P.q (Model.genMap S.p₂ S.h₂) (Model.genMap_q S.p₂ S.h₂) h3 g3 v x]
  refine (cupK P hM S X Y Z hZ (fun a => Module.finBasis K (Hdg M.q a i))
    (fun a => Module.finBasis K (Hdg M.q a j)) A _).trans ?_
  refine Finset.sum_eq_zero fun p _ => Finset.sum_eq_zero fun s _ => Finset.sum_eq_zero fun s' _ => ?_
  have hm : p.1.1 + p.1.2 = A := Finset.HasAntidiagonal.mem_antidiagonal.1 p.2
  rw [assoc hm rfl rfl rfl, hsl.2 p.1.1 i (p.1.2 + a') (j + n) (by omega) (by omega)
    (fun h => hj (by have := congrArg Prod.snd h; dsimp only at this; omega))]
  simp only [map_zero, mul_zero]

end CrystallineSemistableComparison.Onto

end
