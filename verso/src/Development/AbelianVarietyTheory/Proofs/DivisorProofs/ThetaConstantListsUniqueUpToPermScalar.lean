import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SymTupOne
import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.MinSt2
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaConstantUniqueAndLinearInSectionStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.UMin.ThUniq

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => rw [pow_zero, pow_zero, MonObj.comp_one]`. Consider the case `succ n ih => rw [pow_succ, pow_succ, MonObj.comp_mul, ih]`.
-/
theorem comp_pow' {S : Scheme.{0}} {A T T₀ : Over S} [GrpObj A] (ρ : T₀ ⟶ T) (x : T ⟶ A) (n : ℕ) :
    ρ ≫ x ^ n = (ρ ≫ x) ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, MonObj.comp_one]
  | succ n ih => rw [pow_succ, pow_succ, MonObj.comp_mul, ih]

/- English proof (translation)
Establish `key : ∀ b, ∃ a, q b = pt a`. Introduce `b`. Set `i` to `algebraMap K (AlgebraicClosure K)`. Set `u : Over.mk (spMap i ≫ x) ⟶ Over.mk x` to `Over.homMk (spMap i) rfl`. Establish `hp : (u ≫ q b) ^ (m ^ 2) = 1`.

Rewrite using `[← comp_pow', (h'.2.1 b).1, MonObj.comp_one]`. Take `⟨a, ha⟩` from `h.2.2 (AlgebraicClosure K) i (u ≫ q b) hp`. Use `⟨a, Over.OverMorphism.ext ?_⟩` and prove the remaining obligations. Establish `: Epi (spMap i)` using `Flat.epi_of_flat_of_surjective _`. Conclude with `(cancel_epi (spMap i)).1 (by rw [← ha, Over.comp_left]; rfl)`.

Use `choose f hf using key`. Establish `hinj : Function.Injective f` using `fun b b' e => h'.1 ((hf b).trans ((congrArg pt e).trans (hf b').symm))`. Conclude with `⟨Equiv.ofBijective f (Finite.injective_iff_bijective.1 hinj), hf⟩`.
-/
theorem exists_perm_pts {S : Scheme.{0}} {G : Over S} [GrpObj G] {L : LB G.left} {ρ : LB.Gen (L.pull (eSec G))}
    {m : ℕ} {K : Type} [Field K] {x : Sp K ⟶ S} {θ θ' : SecAt G L x} {N : ℕ} {pt q : Fin N → (Over.mk x ⟶ G)}
    {c d : Fin N → K} (h : ThList G L ρ m x θ pt c) (h' : ThList G L ρ m x θ' q d) :
    ∃ σ : Equiv.Perm (Fin N), ∀ b, q b = pt (σ b) := by
  have key : ∀ b, ∃ a, q b = pt a := by
    intro b
    let i := algebraMap K (AlgebraicClosure K)
    let u : Over.mk (spMap i ≫ x) ⟶ Over.mk x := Over.homMk (spMap i) rfl
    have hp : (u ≫ q b) ^ (m ^ 2) = 1 := by
      rw [← comp_pow', (h'.2.1 b).1, MonObj.comp_one]
    obtain ⟨a, ha⟩ := h.2.2 (AlgebraicClosure K) i (u ≫ q b) hp
    refine ⟨a, Over.OverMorphism.ext ?_⟩
    have : Epi (spMap i) := Flat.epi_of_flat_of_surjective _
    exact (cancel_epi (spMap i)).1 (by rw [← ha, Over.comp_left]; rfl)
  choose f hf using key
  have hinj : Function.Injective f := fun b b' e => h'.1 ((hf b).trans ((congrArg pt e).trans (hf b').symm))
  exact ⟨Equiv.ofBijective f (Finite.injective_iff_bijective.1 hinj), hf⟩

end GlobalTheory.UMin.ThUniq

namespace GlobalTheory.UMin.ThUniq

/- English proof (translation)
Introduce `S G _ _ L ρ hL hρ g m m' N N' K _ x hm hmK hm' hmK' hpol`. Establish `tv : ∀ (k : ℕ), Odd k → (k : K) ≠ 0 → ∀ (θ θ' : SecAt G L x) (p : Over.mk x ⟶ G) (a c c' : K), SecM.ofSec G θ' = @id Γ((Over.mk x).left, ⊤) (GlobalTheory.ZH.fn a) • SecM.ofSec G θ → ThG G L ρ k θ p (GlobalTheory.ZH.fn c) → ThG G L ρ k θ' p (GlobalTheory.ZH.fn c') → c' = a * c` using `fun k hk hkK θ θ' p a c c' hs hc hc' => (GlobalTheory.T.thetaConstant_unique_and_linear_in_section S G L ρ hL hρ g k K x θ θ' p a c c' hk hkK hpol hs hc).1 hc'`. Establish `gen : ∀ θ θ' : SecAt G L x, IsGenSec G L _ θ → ∃ a : K, SecM.ofSec G θ' = @id Γ((Over.mk x).left, ⊤) (GlobalTheory.ZH.fn a) • SecM.ofSec G θ`. Introduce `θ θ' h`. Take `⟨r, hr⟩` from `h θ'`.

Use `⟨(Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom r, ?_⟩` and prove the remaining obligations. Establish `e : @id Γ((Over.mk x).left, ⊤) (GlobalTheory.ZH.fn ((Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom r)) = r` using `by show ((Scheme.ΓSpecIso (CommRingCat.of K)).hom ≫ (Scheme.ΓSpecIso (CommRingCat.of K)).inv).hom r = r`. Rewrite using `[Iso.hom_inv_id]`. Both sides reduce to the same expression. Rewrite using `[e]`.

Conclude with `Subtype.ext (funext hr)`. Use `⟨fun θ pt pt' c d h h' => ?_, fun c d c' d' H H' => ?_⟩` and prove the remaining obligations. Take `⟨σ, hσ⟩` from `exists_perm_pts h h'`. Use `⟨σ, fun b => ?_⟩` and prove the remaining obligations. Establish `e1 : SecM.ofSec G θ = @id Γ((Over.mk x).left, ⊤) (GlobalTheory.ZH.fn (1 : K)) • SecM.ofSec G θ`.

Rewrite using `[show @id Γ((Over.mk x).left, ⊤) (GlobalTheory.ZH.fn (1 : K)) = 1 from map_one _, one_smul]`. Rewrite using `[tv m hm hmK θ θ (pt (σ b)) 1 (c (σ b)) (d b) e1 (h.2.1 (σ b)) (by rw [← hσ b]; exact h'.2.1 b), _root_.one_mul]`. Take `⟨θ, pt, pt', hg, h1, h1'⟩` from `H`. Take `⟨θ₂, q, q', hg₂, h2, h2'⟩` from `H'`. Take `⟨σ, hσ⟩` from `exists_perm_pts h1 h2`.

Take `⟨σ', hσ'⟩` from `exists_perm_pts h1' h2'`. Take `⟨a₀, ha₀⟩` from `gen θ θ₂ hg`. Take `⟨a₁, ha₁⟩` from `gen θ₂ θ hg₂`. Establish `E : ∀ b, d b = a₀ * c (σ b)` using `fun b => tv m hm hmK θ θ₂ _ a₀ _ _ ha₀ (h1.2.1 (σ b)) (by rw [← hσ b]; exact h2.2.1 b)`. Establish `E' : ∀ b, d' b = a₀ * c' (σ' b)` using `fun b => tv m' hm' hmK' θ θ₂ _ a₀ _ _ ha₀ (h1'.2.1 (σ' b)) (by rw [← hσ' b]; exact h2'.2.1 b)`.

Distinguish the cases in `h0 : a₀ = 0`. Establish `F : ∀ b, c (σ b) = a₁ * d b` using `fun b => tv m hm hmK θ₂ θ _ a₁ _ _ ha₁ (by rw [← hσ b]; exact h2.2.1 b) (h1.2.1 (σ b))`. Establish `F' : ∀ b, c' (σ' b) = a₁ * d' b` using `fun b => tv m' hm' hmK' θ₂ θ _ a₁ _ _ ha₁ (by rw [← hσ' b]; exact h2'.2.1 b) (h1'.2.1 (σ' b))`. Use `⟨1, σ, σ', one_ne_zero, fun b => ?_, fun b => ?_⟩` and prove the remaining obligations. Establish `e` using `E b`.

Rewrite `e` using `[h0, MulZeroClass.zero_mul]`. Rewrite using `[F b, e, MulZeroClass.mul_zero, MulZeroClass.mul_zero]`. Establish `e` using `E' b`. Rewrite `e` using `[h0, MulZeroClass.zero_mul]`. Rewrite using `[F' b, e, MulZeroClass.mul_zero, MulZeroClass.mul_zero]`.

Conclude with `⟨a₀, σ, σ', h0, E, E'⟩`.
-/
theorem theta_lists_unique : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : LB G.left) (ρ : LB.Gen (L.pull (eSec G))), L.IsLB → ρ.IsGen → ∀ (g m m' N N' : ℕ) (K : Type) [Field K] (x : Sp K ⟶ S), Odd m → (m : K) ≠ 0 → Odd m' → (m' : K) ≠ 0 → PolFib G L g x → (∀ (θ : SecAt G L x) (pt pt' : Fin N → (Over.mk x ⟶ G)) (c d : Fin N → K), ThList G L ρ m x θ pt c → ThList G L ρ m x θ pt' d → ∃ σ : Equiv.Perm (Fin N), ∀ b, d b = c (σ b)) ∧ ∀ (c d : Fin N → K) (c' d' : Fin N' → K), HasTh₂ G L ρ m m' x c c' → HasTh₂ G L ρ m m' x d d' → ∃ (a : K) (σ : Equiv.Perm (Fin N)) (σ' : Equiv.Perm (Fin N')), a ≠ 0 ∧ (∀ b, d b = a * c (σ b)) ∧ ∀ b, d' b = a * c' (σ' b) := by
  intro S G _ _ L ρ hL hρ g m m' N N' K _ x hm hmK hm' hmK' hpol
  have tv : ∀ (k : ℕ), Odd k → (k : K) ≠ 0 → ∀ (θ θ' : SecAt G L x) (p : Over.mk x ⟶ G) (a c c' : K),
      SecM.ofSec G θ' = @id Γ((Over.mk x).left, ⊤) (GlobalTheory.ZH.fn a) • SecM.ofSec G θ →
      ThG G L ρ k θ p (GlobalTheory.ZH.fn c) → ThG G L ρ k θ' p (GlobalTheory.ZH.fn c') → c' = a * c :=
    fun k hk hkK θ θ' p a c c' hs hc hc' =>
      (GlobalTheory.T.thetaConstant_unique_and_linear_in_section S G L ρ hL hρ g k K x θ θ' p a c c' hk hkK hpol hs hc).1 hc'
  have gen : ∀ θ θ' : SecAt G L x, IsGenSec G L _ θ →
      ∃ a : K, SecM.ofSec G θ' = @id Γ((Over.mk x).left, ⊤) (GlobalTheory.ZH.fn a) • SecM.ofSec G θ := by
    intro θ θ' h
    obtain ⟨r, hr⟩ := h θ'
    refine ⟨(Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom r, ?_⟩
    have e : @id Γ((Over.mk x).left, ⊤) (GlobalTheory.ZH.fn ((Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom r)) = r := by
      show ((Scheme.ΓSpecIso (CommRingCat.of K)).hom ≫ (Scheme.ΓSpecIso (CommRingCat.of K)).inv).hom r = r
      rw [Iso.hom_inv_id]; rfl
    rw [e]
    exact Subtype.ext (funext hr)
  refine ⟨fun θ pt pt' c d h h' => ?_, fun c d c' d' H H' => ?_⟩
  · obtain ⟨σ, hσ⟩ := exists_perm_pts h h'
    refine ⟨σ, fun b => ?_⟩
    have e1 : SecM.ofSec G θ = @id Γ((Over.mk x).left, ⊤) (GlobalTheory.ZH.fn (1 : K)) • SecM.ofSec G θ := by
      rw [show @id Γ((Over.mk x).left, ⊤) (GlobalTheory.ZH.fn (1 : K)) = 1 from map_one _, one_smul]
    rw [tv m hm hmK θ θ (pt (σ b)) 1 (c (σ b)) (d b) e1 (h.2.1 (σ b)) (by rw [← hσ b]; exact h'.2.1 b), _root_.one_mul]
  · obtain ⟨θ, pt, pt', hg, h1, h1'⟩ := H
    obtain ⟨θ₂, q, q', hg₂, h2, h2'⟩ := H'
    obtain ⟨σ, hσ⟩ := exists_perm_pts h1 h2
    obtain ⟨σ', hσ'⟩ := exists_perm_pts h1' h2'
    obtain ⟨a₀, ha₀⟩ := gen θ θ₂ hg
    obtain ⟨a₁, ha₁⟩ := gen θ₂ θ hg₂
    have E : ∀ b, d b = a₀ * c (σ b) := fun b =>
      tv m hm hmK θ θ₂ _ a₀ _ _ ha₀ (h1.2.1 (σ b)) (by rw [← hσ b]; exact h2.2.1 b)
    have E' : ∀ b, d' b = a₀ * c' (σ' b) := fun b =>
      tv m' hm' hmK' θ θ₂ _ a₀ _ _ ha₀ (h1'.2.1 (σ' b)) (by rw [← hσ' b]; exact h2'.2.1 b)
    by_cases h0 : a₀ = 0
    · have F : ∀ b, c (σ b) = a₁ * d b := fun b =>
        tv m hm hmK θ₂ θ _ a₁ _ _ ha₁ (by rw [← hσ b]; exact h2.2.1 b) (h1.2.1 (σ b))
      have F' : ∀ b, c' (σ' b) = a₁ * d' b := fun b =>
        tv m' hm' hmK' θ₂ θ _ a₁ _ _ ha₁ (by rw [← hσ' b]; exact h2'.2.1 b) (h1'.2.1 (σ' b))
      refine ⟨1, σ, σ', one_ne_zero, fun b => ?_, fun b => ?_⟩
      · have e := E b
        rw [h0, MulZeroClass.zero_mul] at e
        rw [F b, e, MulZeroClass.mul_zero, MulZeroClass.mul_zero]
      · have e := E' b
        rw [h0, MulZeroClass.zero_mul] at e
        rw [F' b, e, MulZeroClass.mul_zero, MulZeroClass.mul_zero]
    · exact ⟨a₀, σ, σ', h0, E, E'⟩

end GlobalTheory.UMin.ThUniq
