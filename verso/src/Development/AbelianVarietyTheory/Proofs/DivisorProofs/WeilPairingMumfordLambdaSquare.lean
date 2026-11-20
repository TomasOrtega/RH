import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TorMatch
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaLinComb
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsAlternatingSkewNatural
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsPELTripleOfDenseFibres
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbelianSchemeGerms
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaOfTranslDiff
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.LamPairing

section Coords

variable {S : Scheme.{0}} (G : Over S) [GrpObj G] [IsCommMonObj G]

/- English proof (translation)
Use `revert I`. Evaluate the decidable proposition.
-/
theorem finset_fin_two (I : Finset (Fin 2)) : I = ∅ ∨ I = {0} ∨ I = {1} ∨ I = {0, 1} := by
  revert I; decide

/- English proof (translation)
Simplify using `[psum, pzero]`. Both sides reduce to the same expression.
-/
theorem psum_empty : psum G (x2 G) ∅ = 1 := by
  simp [psum, pzero]; rfl

/- English proof (translation)
Simplify using `[psum, padd, pzero, x2, List.finRange]`.
-/
theorem psum_zero : psum G (x2 G) {0} = fst G G := by
  simp [psum, padd, pzero, x2, List.finRange]

/- English proof (translation)
Simplify using `[psum, padd, pzero, x2, List.finRange]`.
-/
theorem psum_one : psum G (x2 G) {1} = snd G G := by
  simp [psum, padd, pzero, x2, List.finRange]

/- English proof (translation)
Simplify using `[psum, padd, pzero, x2, List.finRange]`. Use `show μ[G] = lift (fst G G) (snd G G) ≫ μ[G]`. Rewrite using `[lift_fst_snd, Category.id_comp]`.
-/
theorem psum_both : psum G (x2 G) {0, 1} = fst G G * snd G G := by
  simp [psum, padd, pzero, x2, List.finRange]
  show μ[G] = lift (fst G G) (snd G G) ≫ μ[G]
  rw [lift_fst_snd, Category.id_comp]

/- English proof (translation)
Break down `finset_fin_two I with rfl | rfl | rfl | rfl` into its components or cases. Rewrite using `[psum_empty]`. Conclude with `inferInstanceAs (IsMonHom (toUnit (G2 G) ≫ η[G]))`. Rewrite using `[psum_zero]`. Use `infer_instance`.

Rewrite using `[psum_one]`. Use `infer_instance`. Rewrite using `[psum_both] show IsMonHom (lift (fst G G) (snd G G) ≫ μ[G])`. Rewrite using `[lift_fst_snd, Category.id_comp]`. Use `infer_instance`.
-/
theorem squareGroupPartialSum_isMonHom (I : Finset (Fin 2)) : IsMonHom (psum G (x2 G) I) := by
  rcases finset_fin_two I with rfl | rfl | rfl | rfl
  · rw [psum_empty]; exact inferInstanceAs (IsMonHom (toUnit (G2 G) ≫ η[G]))
  · rw [psum_zero]; infer_instance
  · rw [psum_one]; infer_instance
  · rw [psum_both]
    show IsMonHom (lift (fst G G) (snd G G) ≫ μ[G])
    rw [lift_fst_snd, Category.id_comp]
    infer_instance

end Coords

/- English proof (translation)
Rewrite using `[← Fintype.prod_equiv Equiv.ulift.symm (fun I => f (Equiv.ulift.symm I)) f (fun _ => rfl)]`. Establish `h : (Finset.univ : Finset (Finset (Fin 2))) = {∅, {0}, {1}, {0, 1}}` using `by decide`. Rewrite using `[h, Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_singleton]`. Simplify using `only [Equiv.ulift_symm_apply]`. The two sides agree by associativity and commutativity.
-/
theorem prod_ulift_finset_fin_two {M : Type} [CommMonoid M] (f : ULift.{0} (Finset (Fin 2)) → M) :
    ∏ I, f I = f ⟨∅⟩ * f ⟨{0}⟩ * f ⟨{1}⟩ * f ⟨{0, 1}⟩ := by
  rw [← Fintype.prod_equiv Equiv.ulift.symm (fun I => f (Equiv.ulift.symm I)) f (fun _ => rfl)]
  have h : (Finset.univ : Finset (Finset (Fin 2))) = {∅, {0}, {1}, {0, 1}} := by decide
  rw [h, Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_singleton]
  simp only [Equiv.ulift_symm_apply]
  ac_rfl

/- English proof (translation)
Establish `hW : WeilSt` using `GlobalTheory.firstFiveLaws.1.weil`. Take `⟨a, ha, -⟩` from `(hW S P n T).1 x₁ y₁ hx₁ hy₁`. Take `⟨b, hb, -⟩` from `(hW S P n T).1 x₂ y₂ hx₂ hy₂`. Establish `hmul` using `(hW S P n T).2.1`. Establish `h₀ : WeilIs P.A P.L n 1 1 1` using `(hW S P n T).2.2.1 1 (one_pow n)`.

Establish `hr : ∀ (x y y' : T ⟶ P.A) (c c' : Γ(T.left, ⊤)ˣ), WeilIs P.A P.L n x y c → WeilIs P.A P.L n x y' c' → WeilIs P.A P.L n x (y * y') (c * c')` using `fun x y y' c c' hc hc' => by`. Use `CommPairing.weilIs_symm P.isLB (hmul _ _ _ _ _ (CommPairing.weilIs_symm P.isLB hc) (CommPairing.weilIs_symm P.isLB hc'))` as an intermediate fact. Rewrite `this` using `[← mul_inv, inv_inv]`. Then use the resulting hypothesis. Establish `h₁₂ : WeilIs P.A P.L n (x₁ * x₂) (y₁ * y₂) (a * c₁ * (c₂ * b))` using `hmul _ _ _ _ _ (hr _ _ _ _ _ ha h₁) (hr _ _ _ _ _ h₂ hb)`. Establish `hA : IsAbelianScheme (G2 P.A)` using `AbelianSchemeGerms.isAbelianScheme_tensor _ _ P.isAb P.isAb`.

Set `c : ULift.{0} (Finset (Fin 2)) → Γ(T.left, ⊤)ˣ` to `fun I => (if (0 : Fin 2) ∈ I.down then a else 1) * (if (1 : Fin 2) ∈ I.down then b else 1) * (if (0 : Fin 2) ∈ I.down ∧ (1 : Fin 2) ∈ I.down then c₁ * c₂ else 1)`. Establish `key` using `PairingComb.weilIs_linComb (D := P.L) GlobalTheory.globalFns_holds hA P.isLB (fun I : ULift.{0} (Finset (Fin 2)) => psum P.A (x2 P.A) I.down) (fun I => squareGroupPartialSum_isMonHom P.A I.down) (fun I => (-1) ^ (2 - I.down.card)) (n := n) (x := lift x₁ x₂) (y := lift y₁ y₂) c (b …`. Introduce and unpack `⟨I⟩`. Break down `finset_fin_two I with rfl | rfl | rfl | rfl` into its components or cases. Simplify using `only [c, psum_empty, MonObj.comp_one]`.

Simplify using `using h₀`. Simplify using `only [c, psum_zero, lift_fst]`. Simplify using `using ha`. Simplify using `only [c, psum_one, lift_snd]`. Simplify using `using hb`.

Simplify using `only [c, psum_both, MonObj.comp_mul, lift_fst, lift_snd]`. Use `h₁₂ using 1` and compare the differences between its conclusion and the goal. Simplify using `only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true, and_self, if_true]`. Use the proof step `ac_rfl)`. Establish `e : ∏ I, c I ^ ((-1 : ℤ) ^ (2 - I.down.card)) = c₁ * c₂`.

Rewrite using `[prod_ulift_finset_fin_two]`. Simplify using `[c]`. Rewrite using `[← mul_inv, inv_mul_cancel_left]`. Rewrite `key` using `[e]`. Conclude with `key`.
-/
theorem weilIs_lam (S : Scheme.{0}) [IsLocallyNoetherian S] (P : PolAV S) (n : ℕ) (T : Over S)
    (x₁ x₂ y₁ y₂ : T ⟶ P.A) (hx₁ : x₁ ^ n = 1) (hx₂ : x₂ ^ n = 1) (hy₁ : y₁ ^ n = 1) (hy₂ : y₂ ^ n = 1)
    (c₁ c₂ : Γ(T.left, ⊤)ˣ) (h₁ : WeilIs P.A P.L n x₁ y₂ c₁) (h₂ : WeilIs P.A P.L n x₂ y₁ c₂) :
    WeilIs (G2 P.A) (abelian₂ P.A P.L) n (lift x₁ x₂) (lift y₁ y₂) (c₁ * c₂) := by
  have hW : WeilSt := GlobalTheory.firstFiveLaws.1.weil
  obtain ⟨a, ha, -⟩ := (hW S P n T).1 x₁ y₁ hx₁ hy₁
  obtain ⟨b, hb, -⟩ := (hW S P n T).1 x₂ y₂ hx₂ hy₂
  have hmul := (hW S P n T).2.1
  have h₀ : WeilIs P.A P.L n 1 1 1 := (hW S P n T).2.2.1 1 (one_pow n)

  have hr : ∀ (x y y' : T ⟶ P.A) (c c' : Γ(T.left, ⊤)ˣ), WeilIs P.A P.L n x y c → WeilIs P.A P.L n x y' c' →
      WeilIs P.A P.L n x (y * y') (c * c') := fun x y y' c c' hc hc' => by
    have := CommPairing.weilIs_symm P.isLB
      (hmul _ _ _ _ _ (CommPairing.weilIs_symm P.isLB hc) (CommPairing.weilIs_symm P.isLB hc'))
    rwa [← mul_inv, inv_inv] at this
  have h₁₂ : WeilIs P.A P.L n (x₁ * x₂) (y₁ * y₂) (a * c₁ * (c₂ * b)) :=
    hmul _ _ _ _ _ (hr _ _ _ _ _ ha h₁) (hr _ _ _ _ _ h₂ hb)
  have hA : IsAbelianScheme (G2 P.A) := AbelianSchemeGerms.isAbelianScheme_tensor _ _ P.isAb P.isAb
  let c : ULift.{0} (Finset (Fin 2)) → Γ(T.left, ⊤)ˣ := fun I =>
    (if (0 : Fin 2) ∈ I.down then a else 1) * (if (1 : Fin 2) ∈ I.down then b else 1) *
      (if (0 : Fin 2) ∈ I.down ∧ (1 : Fin 2) ∈ I.down then c₁ * c₂ else 1)
  have key := PairingComb.weilIs_linComb (D := P.L) GlobalTheory.globalFns_holds hA P.isLB
    (fun I : ULift.{0} (Finset (Fin 2)) => psum P.A (x2 P.A) I.down) (fun I => squareGroupPartialSum_isMonHom P.A I.down)
    (fun I => (-1) ^ (2 - I.down.card)) (n := n) (x := lift x₁ x₂) (y := lift y₁ y₂) c (by
      rintro ⟨I⟩
      rcases finset_fin_two I with rfl | rfl | rfl | rfl
      · simp only [c, psum_empty, MonObj.comp_one]
        simpa using h₀
      · simp only [c, psum_zero, lift_fst]
        simpa using ha
      · simp only [c, psum_one, lift_snd]
        simpa using hb
      · simp only [c, psum_both, MonObj.comp_mul, lift_fst, lift_snd]
        convert h₁₂ using 1
        simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true, and_self, if_true]
        ac_rfl)
  have e : ∏ I, c I ^ ((-1 : ℤ) ^ (2 - I.down.card)) = c₁ * c₂ := by
    rw [prod_ulift_finset_fin_two]
    simp [c]
    rw [← mul_inv, inv_mul_cancel_left]
  rw [e] at key
  exact key

end GlobalTheory.LamPairing
