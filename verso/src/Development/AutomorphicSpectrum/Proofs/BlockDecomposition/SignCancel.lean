import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.KummerCupProducts.FirstChernCompatibleSystem

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry Opposite CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

namespace GlobalTheory.CompanionTheory.Staircase

variable {R : Type} [CommRing R] {C : Type 1} [Category.{0} C]

/- English proof (translation)
The claim follows from `(hT.ι_nat _ _).symm`.
-/
theorem term_ιC {F : C ⥤ ModuleCat.{0} R} (T : Res.{1} F) (hT : T.Good) {p n : ℕ}
    (s : ComposableArrows C n) (z : Cn F p) (g : Fin (p + 1) → Fin (n + 1)) (hg : Monotone g) :
    term (T.K 0) s (T.ιC p z) g hg = T.ι _ (term F s z g hg) :=
  (hT.ι_nat _ _).symm

/- English proof (translation)
The claim follows from `(hT.dv_nat t _ _).symm`.
-/
theorem term_dvC {F : C ⥤ ModuleCat.{0} R} (T : Res.{1} F) (hT : T.Good) (t : ℕ) {p n : ℕ}
    (s : ComposableArrows C n) (a : Cn (T.K t) p) (g : Fin (p + 1) → Fin (n + 1)) (hg : Monotone g) :
    term (T.K (t + 1)) s (T.dvC t p a) g hg = T.dv t _ (term (T.K t) s a g hg) :=
  (hT.dv_nat t _ _).symm

/- English proof (translation)
Substitute `h` using the available equality. Rewrite using `[pow_add, mul_comm ((-1 : ℤ) ^ i), mul_assoc, ← mul_pow]`. Simplify using the standard rewrite rules.
-/
theorem sign_cancel {i k r : ℕ} (h : i + k = r) : (-1 : ℤ) ^ r * (-1 : ℤ) ^ i = (-1 : ℤ) ^ k := by
  subst h
  rw [pow_add, mul_comm ((-1 : ℤ) ^ i), mul_assoc, ← mul_pow]
  simp

/- English proof (translation)
Introduce `hL hC R _ C _ F₁ F₂ F₃ T₁ T₂ T₃ P μ g₁ g₂ i j n hn z z' hz t`. Proceed by induction on `t with`. Consider the case `zero`. Introduce `k r h y hy`. Take `⟨rfl, rfl⟩` from `hy`.

Substitute `h` using the available equality. Substitute `hn` using the available equality. Use `⟨rfl, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `s`. Express the relevant statement in the definitionally equal form `T₃.ι _ (P.μ _ (term F₁ s z _ _) (term F₂ s z' _ _)) = (μ.μ 0 0 0 (zero_add 0)).μ _ (term (T₁.K 0) s (T₁.ιC i z) _ _) (term (T₂.K 0) s (T₂.ιC _ z') _ _)`.

Rewrite using `[term_ιC T₁ g₁, term_ιC T₂ g₂]`. Conclude with `(μ.ι _ _ _).symm`. Consider the case `succ t ih`. Introduce `k r h y hy`. Take `⟨a, rfl, ha⟩` from `hy`.

Establish `hd : d (T₁.K 0) i (T₁.ιC i z) = 0`. Rewrite using `[(hC R C F₁ T₁ g₁).1, hz, map_zero]`. Use `⟨(μ.μ 0 t t (zero_add t)).cupC h (T₁.ιC i z) a, ?_, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `s`. Express the relevant statement in the definitionally equal form `T₃.dv t _ ((μ.μ 0 t t (zero_add t)).μ _ (term (T₁.K 0) s (T₁.ιC i z) _ _) (term (T₂.K t) s a _ _)) = (μ.μ 0 (t + 1) (t + 1) (zero_add (t + 1))).μ _ (term (T₁.K 0) s (T₁.ιC i z) _ _) (term (T₂.K (t + 1)) s (T₂.dvC t k a) _ _)`.

Rewrite using `[μ.leib 0 t t (zero_add t), term_dvC T₂ g₂, term_ιC T₁ g₁, (g₁.ex0 _ _).mpr ⟨_, rfl⟩, map_zero, LinearMap.zero_apply, zero_add, pow_zero, one_smul]`. Establish `e` using `hL R C (T₁.K 0) (T₂.K t) (T₃.K t) (μ.μ 0 t t (zero_add t)) i k r h (T₁.ιC i z) a`. Establish `key` using `ih (k + 1) (r + 1) (by omega) ((-1 : ℤ) ^ k • d (T₂.K t) k a) ha`. Establish `e' : (-1 : ℤ) ^ r • d (T₃.K t) r ((μ.μ 0 t t (zero_add t)).cupC h (T₁.ιC i z) a) = (μ.μ 0 t t (zero_add t)).cupC (show i + (k + 1) = r + 1 by omega) (T₁.ιC i z) ((-1 : ℤ) ^ k • d (T₂.K t) k a)`. Rewrite using `[e, hd, map_zero, LinearMap.zero_apply, zero_add, smul_smul, sign_cancel h, map_zsmul]`.

Rewrite using `[e']`. Conclude with `key`.
-/
theorem stCupB : CupLeib.{1} → StCol → StCupB := by
  intro hL hC R _ C _ F₁ F₂ F₃ T₁ T₂ T₃ P μ g₁ g₂ i j n hn z z' hz t
  induction t with
  | zero =>
    intro k r h y hy
    obtain ⟨rfl, rfl⟩ := hy
    subst h
    subst hn
    refine ⟨rfl, ?_⟩
    funext s
    change T₃.ι _ (P.μ _ (term F₁ s z _ _) (term F₂ s z' _ _)) =
      (μ.μ 0 0 0 (zero_add 0)).μ _ (term (T₁.K 0) s (T₁.ιC i z) _ _) (term (T₂.K 0) s (T₂.ιC _ z') _ _)
    rw [term_ιC T₁ g₁, term_ιC T₂ g₂]
    exact (μ.ι _ _ _).symm
  | succ t ih =>
    intro k r h y hy
    obtain ⟨a, rfl, ha⟩ := hy
    have hd : d (T₁.K 0) i (T₁.ιC i z) = 0 := by
      rw [(hC R C F₁ T₁ g₁).1, hz, map_zero]
    refine ⟨(μ.μ 0 t t (zero_add t)).cupC h (T₁.ιC i z) a, ?_, ?_⟩
    · funext s
      change T₃.dv t _ ((μ.μ 0 t t (zero_add t)).μ _ (term (T₁.K 0) s (T₁.ιC i z) _ _) (term (T₂.K t) s a _ _)) =
        (μ.μ 0 (t + 1) (t + 1) (zero_add (t + 1))).μ _ (term (T₁.K 0) s (T₁.ιC i z) _ _)
          (term (T₂.K (t + 1)) s (T₂.dvC t k a) _ _)
      rw [μ.leib 0 t t (zero_add t), term_dvC T₂ g₂, term_ιC T₁ g₁,
        (g₁.ex0 _ _).mpr ⟨_, rfl⟩, map_zero, LinearMap.zero_apply, zero_add, pow_zero, one_smul]
    · have e := hL R C (T₁.K 0) (T₂.K t) (T₃.K t) (μ.μ 0 t t (zero_add t)) i k r h (T₁.ιC i z) a
      have key := ih (k + 1) (r + 1) (by omega) ((-1 : ℤ) ^ k • d (T₂.K t) k a) ha
      have e' : (-1 : ℤ) ^ r • d (T₃.K t) r ((μ.μ 0 t t (zero_add t)).cupC h (T₁.ιC i z) a) =
          (μ.μ 0 t t (zero_add t)).cupC (show i + (k + 1) = r + 1 by omega) (T₁.ιC i z)
            ((-1 : ℤ) ^ k • d (T₂.K t) k a) := by
        rw [e, hd, map_zero, LinearMap.zero_apply, zero_add, smul_smul, sign_cancel h, map_zsmul]
      rw [e']
      exact key

end GlobalTheory.CompanionTheory.Staircase
