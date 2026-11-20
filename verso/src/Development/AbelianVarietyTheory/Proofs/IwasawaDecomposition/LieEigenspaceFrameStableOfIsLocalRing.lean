import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TriIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsStalkFactor
import Formalism.LocalToGlobal.ProjectiveLattices.MulCMemSec
import Formalism.LocalToGlobal.ProjectiveLattices.AllTest

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ShFam.EigStable

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj GlobalTheory.LieLocBasis GlobalTheory.ShFam.EigLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Chart (tvec tmap eigLat IsUnivChart scaleD sp)

attribute [local instance] Over.cartesianMonoidalCategory

/- English proof (translation)
Use `choose M hM using fun j : Fin n => (hb _ (hP (Pi.single j 1))).exists`. Establish `hs : ∀ {R : Type} [CommRing R] (a : Fin n → R), ∑ j, a j • (Pi.single j 1 : Fin n → R) = a` using `fun a => by`. Use function extensionality and compare the values at `i`. Simplify using `[Finset.sum_apply, Pi.single_apply]`. Establish `hinv : ∀ i, (fun i' => ∑ j, e i j * M j i') = Pi.single i 1` using `fun i => by`.

Use `(hb _ (he i)).unique ?_ ?_` and prove the remaining obligations. Use `conv_lhs => rw [← he i, ← hs (e i), map_sum]`. Simplify using `only [map_smul, hM, Finset.smul_sum, Finset.sum_smul, smul_smul]`. Conclude with `Finset.sum_comm`. Simplify using `[Pi.single_apply]`.

Establish `h1 : ∀ j, P' (Pi.single j 1) = ∑ i, ψ (M j i) • (ψ ∘ e i)` using `fun j => by`. Rewrite using `[show (Pi.single j 1 : Fin n → k) = ψ ∘ Pi.single j 1 from funext fun j' => by`. Apply the tactic sequence `by_cases hj : j' = j <;> simp [hj, Pi.single_apply], h, hM]`. Use function extensionality and compare the values at `r`. Simplify using `[Finset.sum_apply]`.

Use `⟨fun i => ∑ j, c' j * ψ (M j i), ?_, fun a ha => ?_⟩` and prove the remaining obligations. Use `show c' = _ conv_lhs => rw [← hc, ← hs c', map_sum]`. Simplify using `only [map_smul, h1, Finset.smul_sum, Finset.sum_smul, smul_smul]`. Conclude with `Finset.sum_comm`. Use function extensionality and compare the values at `i`.

Establish `h2 : ∀ i', ∑ j, ψ (e i' j) * ψ (M j i) = if i = i' then 1 else 0` using `fun i' => by`. Use `congrArg ψ (congrFun (hinv i') i)` as an intermediate fact. Simplify `this` using `[Pi.single_apply, apply_ite ψ]`. Establish `h3 : ∀ j, c' j = ∑ i', a i' * ψ (e i' j)` using `fun j => by`. Use `congrFun ha j` as an intermediate fact.

Simplify `this` using `[Finset.sum_apply]`. Use `show a i = ∑ j, c' j * ψ (M j i)`. Simplify using `only [h3, Finset.sum_mul, _root_.mul_assoc]`. Rewrite using `[Finset.sum_comm]`. Simplify using `only [← Finset.mul_sum, h2]`.

Simplify using the standard rewrite rules.
-/
theorem basis_fixed_bc {L k : Type} [CommRing L] [CommRing k] (ψ : L →+* k) {n m : ℕ}
    (P : Module.End L (Fin n → L)) (P' : Module.End k (Fin n → k)) (hP : ∀ c, P (P c) = P c)
    (h : ∀ c, P' (ψ ∘ c) = ψ ∘ P c) (e : Fin m → Fin n → L) (he : ∀ i, P (e i) = e i)
    (hb : ∀ c, P c = c → ∃! a : Fin m → L, c = ∑ i, a i • e i) (c' : Fin n → k) (hc : P' c' = c') :
    ∃! a : Fin m → k, c' = ∑ i, a i • (ψ ∘ e i) := by
  classical
  choose M hM using fun j : Fin n => (hb _ (hP (Pi.single j 1))).exists
  have hs : ∀ {R : Type} [CommRing R] (a : Fin n → R), ∑ j, a j • (Pi.single j 1 : Fin n → R) = a := fun a => by
    funext i
    simp [Finset.sum_apply, Pi.single_apply]
  have hinv : ∀ i, (fun i' => ∑ j, e i j * M j i') = Pi.single i 1 := fun i => by
    refine (hb _ (he i)).unique ?_ ?_
    · conv_lhs => rw [← he i, ← hs (e i), map_sum]
      simp only [map_smul, hM, Finset.smul_sum, Finset.sum_smul, smul_smul]
      exact Finset.sum_comm
    · simp [Pi.single_apply]
  have h1 : ∀ j, P' (Pi.single j 1) = ∑ i, ψ (M j i) • (ψ ∘ e i) := fun j => by
    rw [show (Pi.single j 1 : Fin n → k) = ψ ∘ Pi.single j 1 from funext fun j' => by
      by_cases hj : j' = j <;> simp [hj, Pi.single_apply], h, hM]
    funext r
    simp [Finset.sum_apply]
  refine ⟨fun i => ∑ j, c' j * ψ (M j i), ?_, fun a ha => ?_⟩
  · show c' = _
    conv_lhs => rw [← hc, ← hs c', map_sum]
    simp only [map_smul, h1, Finset.smul_sum, Finset.sum_smul, smul_smul]
    exact Finset.sum_comm
  · funext i
    have h2 : ∀ i', ∑ j, ψ (e i' j) * ψ (M j i) = if i = i' then 1 else 0 := fun i' => by
      have := congrArg ψ (congrFun (hinv i') i)
      simpa [Pi.single_apply, apply_ite ψ] using this
    have h3 : ∀ j, c' j = ∑ i', a i' * ψ (e i' j) := fun j => by
      have := congrFun ha j
      simpa [Finset.sum_apply] using this
    show a i = ∑ j, c' j * ψ (M j i)
    simp only [h3, Finset.sum_mul, _root_.mul_assoc]
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum, h2]
    simp

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}} {t : SAB H X}
  {l : Level H} (c : Coeff l)

/- English proof (translation)
Establish `: CharZero c.F` using `RingHom.charZero c.F.val.toRingHom`. Take `⟨α, hinj, ⟨f, hf, hfs⟩, hN⟩` from `exists_sepElt (E := E) (F := c.F) c.F.val.toRingHom (embK c) (fun τ a => embK_coe c τ a)`. Establish `key : ∀ (τ : E →+* ℂ) {R : Type} [CommRing R] [Algebra c.F R] {x : Sp R ⟶ X} {xc : ∀ m : ℕ, sp (R₀` using `R) (ReciprocityTheory.ChartRestriction.G.Chart.JetR R (Fin n) m) ⟶ (Over.pullback x).obj t.G} (hx : IsUnivChart _ n xc), (∀ m, proj (rho hx) (embK c) α τ (proj (rho hx) (embK c) α τ m) = proj (rho hx) (embK c) α τ m) ∧ ∀ m, proj (rho hx) (embK c) α τ m = m ↔ m ∈ eig c (algebraMap …`. Establish `e₁ : ∀ m, ReciprocityTheory.ChartRestriction.G.PullbackSections.IsEigV (rho hx) (embK c τ) (proj (rho hx) (embK c) α τ m)` using `fun m => eig_of_alpha _ _ α hN τ (proj_eig_alpha _ _ α hinj f hf hfs τ m)`. Establish `e₂ : ∀ m, ReciprocityTheory.ChartRestriction.G.PullbackSections.IsEigV (rho hx) (embK c τ) m → proj (rho hx) (embK c) α τ m = m` using `fun m hm => by`.

Use `proj_sum_eig (rho hx) (embK c) α hinj (Pi.single τ m) (fun τ' => by` as an intermediate fact. Distinguish the cases in `h : τ' = τ`. Substitute `h` using the available equality. Rewrite using `[Pi.single_eq_same]` and apply the resulting hypothesis. Rewrite using `[Pi.single_eq_of_ne h]`.

Introduce `a`. Use the proof step `simp) τ`. Rewrite `this` using `[Finset.sum_pi_single', if_pos (Finset.mem_univ _), Pi.single_eq_same]`. Then use the resulting hypothesis. Use `⟨fun m => e₂ _ (e₁ m), fun m => ?_⟩` and prove the remaining obligations. Rewrite using `[ReciprocityTheory.ChartRestriction.G.Chart.mem_eigLat_iff]`.

Conclude with `⟨fun h => h ▸ e₁ m, fun h => e₂ m h⟩`. Use `letI : Algebra c.F L := φ.toAlgebra`. Use `letI : Algebra L k := ψ.toAlgebra`. Use `letI : Algebra c.F k := (ψ.comp φ).toAlgebra`. Take `⟨xc', hx', hv⟩` from `vec_bc (S' := k) hx`.

Establish `htm : ∀ (a : 𝓞 E) (cc : Fin n → L), rho hx' a (algebraMap L k ∘ cc) = algebraMap L k ∘ rho hx a cc` using `fun a cc => vec_inj hx' (by show vec t _ xc' (tmap hx' _ _) = vec t _ xc' (_ ∘ tmap hx _ _)`. Rewrite using `[vec_tmap hx', hv, hv, vec_tmap hx, Category.assoc])`. Establish `pw : ∀ (j : ℕ) cc, (rho hx' α ^ j) (algebraMap L k ∘ cc) = algebraMap L k ∘ (rho hx α ^ j) cc` using `fun j => by`. Proceed by induction on `j with`. Consider the case `zero => exact fun _ => rfl`.

Consider the case `succ j ih => intro cc`. Rewrite using `[pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply, ih]`. Conclude with `htm α _`. Establish `pr : ∀ (Q : Polynomial c.F) cc, Polynomial.aeval (rho hx' α) (Q.map (algebraMap c.F k)) (algebraMap L k ∘ cc) = algebraMap L k ∘ Polynomial.aeval (rho hx α) (Q.map (algebraMap c.F L)) cc` using `fun Q cc => by`. Proceed by induction on `Q using Polynomial.induction_on' with`.

Consider the case `add p q hp hq`. Rewrite using `[Polynomial.map_add, Polynomial.map_add, map_add, map_add, LinearMap.add_apply, LinearMap.add_apply, hp, hq]`. Use function extensionality and compare the values at `j`. Simplify using the standard rewrite rules. Consider the case `monomial j a`.

Rewrite using `[Polynomial.map_monomial, Polynomial.map_monomial, Polynomial.aeval_monomial, Polynomial.aeval_monomial, Module.End.mul_apply, Module.End.mul_apply, pw, Module.algebraMap_end_apply, Module.algebraMap_end_apply]`. Use function extensionality and compare the values at `i`. Conclude with `(map_mul (algebraMap L k) _ _).symm`. Conclude with `⟨xc', hx', hv, fun τ => ⟨_, _, (key τ hx).1, pr _, (key τ hx).2, (key τ hx').2⟩⟩`.
-/
theorem exists_proj_bc {L : Type} [CommRing L] [IsLocalRing L] (φ : c.F →+* L) {x : Sp L ⟶ X} {n : ℕ}
    {xc : ∀ m : ℕ, sp (R₀ := L) (ReciprocityTheory.ChartRestriction.G.Chart.JetR L (Fin n) m) ⟶ (Over.pullback x).obj t.G} (hx : IsUnivChart _ n xc)
    {k : Type} [CommRing k] (ψ : L →+* k) :
    ∃ (xc' : ∀ m : ℕ, sp (R₀ := k) (ReciprocityTheory.ChartRestriction.G.Chart.JetR k (Fin n) m) ⟶ (Over.pullback (spMap ψ ≫ x)).obj t.G)
      (hx' : IsUnivChart _ n xc'),
      (∀ cc : Fin n → L, vec t (spMap ψ ≫ x) xc' (ψ ∘ cc) = spMap (dualMap ψ) ≫ vec t x xc cc) ∧
      ∀ τ, ∃ (P : Module.End L (Fin n → L)) (P' : Module.End k (Fin n → k)), (∀ cc, P (P cc) = P cc) ∧
        (∀ cc, P' (ψ ∘ cc) = ψ ∘ P cc) ∧ (∀ cc, P cc = cc ↔ cc ∈ eig c φ hx τ) ∧
        ∀ cc, P' cc = cc ↔ cc ∈ eig c (ψ.comp φ) hx' τ := by
  classical
  have : CharZero c.F := RingHom.charZero c.F.val.toRingHom
  obtain ⟨α, hinj, ⟨f, hf, hfs⟩, hN⟩ :=
    exists_sepElt (E := E) (F := c.F) c.F.val.toRingHom (embK c) (fun τ a => embK_coe c τ a)
  have key : ∀ (τ : E →+* ℂ) {R : Type} [CommRing R] [Algebra c.F R] {x : Sp R ⟶ X}
      {xc : ∀ m : ℕ, sp (R₀ := R) (ReciprocityTheory.ChartRestriction.G.Chart.JetR R (Fin n) m) ⟶ (Over.pullback x).obj t.G}
      (hx : IsUnivChart _ n xc), (∀ m, proj (rho hx) (embK c) α τ (proj (rho hx) (embK c) α τ m) =
          proj (rho hx) (embK c) α τ m) ∧
        ∀ m, proj (rho hx) (embK c) α τ m = m ↔ m ∈ eig c (algebraMap c.F R) hx τ :=
    fun τ {R} _ _ {x xc} hx => by
      have e₁ : ∀ m, ReciprocityTheory.ChartRestriction.G.PullbackSections.IsEigV (rho hx) (embK c τ) (proj (rho hx) (embK c) α τ m) := fun m =>
        eig_of_alpha _ _ α hN τ (proj_eig_alpha _ _ α hinj f hf hfs τ m)
      have e₂ : ∀ m, ReciprocityTheory.ChartRestriction.G.PullbackSections.IsEigV (rho hx) (embK c τ) m → proj (rho hx) (embK c) α τ m = m := fun m hm => by
        have := proj_sum_eig (rho hx) (embK c) α hinj (Pi.single τ m) (fun τ' => by
          by_cases h : τ' = τ
          · subst h; rwa [Pi.single_eq_same]
          · rw [Pi.single_eq_of_ne h]; intro a; simp) τ
        rwa [Finset.sum_pi_single', if_pos (Finset.mem_univ _), Pi.single_eq_same] at this
      refine ⟨fun m => e₂ _ (e₁ m), fun m => ?_⟩
      rw [ReciprocityTheory.ChartRestriction.G.Chart.mem_eigLat_iff]
      exact ⟨fun h => h ▸ e₁ m, fun h => e₂ m h⟩
  letI : Algebra c.F L := φ.toAlgebra
  letI : Algebra L k := ψ.toAlgebra
  letI : Algebra c.F k := (ψ.comp φ).toAlgebra
  obtain ⟨xc', hx', hv⟩ := vec_bc (S' := k) hx
  have htm : ∀ (a : 𝓞 E) (cc : Fin n → L), rho hx' a (algebraMap L k ∘ cc) = algebraMap L k ∘ rho hx a cc :=
    fun a cc => vec_inj hx' (by
      show vec t _ xc' (tmap hx' _ _) = vec t _ xc' (_ ∘ tmap hx _ _)
      rw [vec_tmap hx', hv, hv, vec_tmap hx, Category.assoc])
  have pw : ∀ (j : ℕ) cc, (rho hx' α ^ j) (algebraMap L k ∘ cc) = algebraMap L k ∘ (rho hx α ^ j) cc := fun j => by
    induction j with
    | zero => exact fun _ => rfl
    | succ j ih => intro cc; rw [pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply, ih]; exact htm α _
  have pr : ∀ (Q : Polynomial c.F) cc, Polynomial.aeval (rho hx' α) (Q.map (algebraMap c.F k)) (algebraMap L k ∘ cc) =
      algebraMap L k ∘ Polynomial.aeval (rho hx α) (Q.map (algebraMap c.F L)) cc := fun Q cc => by
    induction Q using Polynomial.induction_on' with
    | add p q hp hq =>
      rw [Polynomial.map_add, Polynomial.map_add, map_add, map_add, LinearMap.add_apply, LinearMap.add_apply, hp, hq]
      funext j; simp
    | monomial j a =>
      rw [Polynomial.map_monomial, Polynomial.map_monomial, Polynomial.aeval_monomial, Polynomial.aeval_monomial,
        Module.End.mul_apply, Module.End.mul_apply, pw, Module.algebraMap_end_apply, Module.algebraMap_end_apply]
      funext i
      exact (map_mul (algebraMap L k) _ _).symm
  exact ⟨xc', hx', hv, fun τ => ⟨_, _, (key τ hx).1, pr _, (key τ hx).2, (key τ hx').2⟩⟩

end GlobalTheory.ShFam.EigStable

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj
  GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.FlagBundle GlobalTheory.ShFam.EigLoc GlobalTheory.LieLocBasis in

/- English proof (translation)
Introduce `E _ _ _ H Dw l Xo c O _ β Z R _ φ x f _ R' _ _ ψ`. Take `⟨n, xc, hx⟩` from `exists_chart Z.t x`. Take `⟨xc', hx', hv, hP⟩` from `GlobalTheory.ShFam.EigStable.exists_proj_bc c φ hx ψ`. Use `choose e he using fun τ i => vec_exists hx (f.v τ i) (f.tan τ i)`. Use `choose P P' hPP hc hP hP' using hP`.

Establish `heig : ∀ τ i, P τ (e τ i) = e τ i` using `fun τ i => (hP τ _).2 ((vec_eig_iff hx _ _).1 (by rw [← he]; exact f.eig τ i))`. Establish `hfv : ∀ τ, f.v τ = fun i => vec Z.t x xc (e τ i)` using `fun τ => funext (he τ)`. Use `⟨⟨fun τ i => vec Z.t (spMap ψ ≫ x) xc' (ψ ∘ e τ i), fun τ i => vec_tan hx' _, fun τ i => (vec_eig_iff hx' _ _).2 ((hP' τ _).1 (by rw [hc, heig])), fun τ w hw hw' => ?_⟩, fun τ i => by rw [he]; exact hv _⟩` and prove the remaining obligations. Take `⟨cc, rfl⟩` from `vec_exists hx' w hw`. Simplify using `only [comb_iff hx']`.

Use `GlobalTheory.ShFam.EigStable.basis_fixed_bc ψ (P τ) (P' τ) (hPP τ) (hc τ) (e τ) (heig τ) (fun c₀ h₀ => ?_) cc ((hP' τ _).2 ((vec_eig_iff hx' _ _).1 hw'))` and prove the remaining obligations. Use `f.basis τ _ (vec_tan hx c₀) ((vec_eig_iff hx _ _).2 ((hP τ _).1 h₀))` as an intermediate fact. Rewrite `this` using `[hfv]`. Simplify `this` using `only [comb_iff hx]`.
-/
theorem GlobalTheory.ShFam.EigStable.stable_of_isLocalRing : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (R : Type) [CommRing R] (φ : c.F →+* R) (x : Sp R ⟶ Z.X) (f : EigFrame Z φ x), IsLocalRing R → f.Stable := by
  intro E _ _ _ H Dw l Xo c O _ β Z R _ φ x f _ R' _ _ ψ
  obtain ⟨n, xc, hx⟩ := exists_chart Z.t x
  obtain ⟨xc', hx', hv, hP⟩ := GlobalTheory.ShFam.EigStable.exists_proj_bc c φ hx ψ
  choose e he using fun τ i => vec_exists hx (f.v τ i) (f.tan τ i)
  choose P P' hPP hc hP hP' using hP
  have heig : ∀ τ i, P τ (e τ i) = e τ i := fun τ i =>
    (hP τ _).2 ((vec_eig_iff hx _ _).1 (by rw [← he]; exact f.eig τ i))
  have hfv : ∀ τ, f.v τ = fun i => vec Z.t x xc (e τ i) := fun τ => funext (he τ)
  refine ⟨⟨fun τ i => vec Z.t (spMap ψ ≫ x) xc' (ψ ∘ e τ i), fun τ i => vec_tan hx' _,
    fun τ i => (vec_eig_iff hx' _ _).2 ((hP' τ _).1 (by rw [hc, heig])), fun τ w hw hw' => ?_⟩,
    fun τ i => by rw [he]; exact hv _⟩
  obtain ⟨cc, rfl⟩ := vec_exists hx' w hw
  simp only [comb_iff hx']
  refine GlobalTheory.ShFam.EigStable.basis_fixed_bc ψ (P τ) (P' τ) (hPP τ) (hc τ) (e τ) (heig τ) (fun c₀ h₀ => ?_) cc
    ((hP' τ _).2 ((vec_eig_iff hx' _ _).1 hw'))
  have := f.basis τ _ (vec_tan hx c₀) ((vec_eig_iff hx _ _).2 ((hP τ _).1 h₀))
  rw [hfv] at this
  simpa only [comb_iff hx] using this
