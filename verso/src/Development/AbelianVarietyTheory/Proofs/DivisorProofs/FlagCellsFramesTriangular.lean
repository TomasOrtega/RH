import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqSpMapEv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvRFrMapOfIsReduced
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemSpanOfPluckerProportional

noncomputable section

namespace GlobalTheory.FlagMod.FieldFlag

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg GlobalTheory.FlagEmb GlobalTheory.ProjSpace
open GlobalTheory.FlagMod.LowRank (ECh Proj str)

/- English proof (translation)
Use `choose a ha hV using h`. Establish `hc : ∀ j, (fun i => (Wm * V) i j) = a j` using `fun j => by`. Establish `e : (fun i => (Wm * V) i j) = Wm.mulVec (fun r => V r j)`. Use function extensionality and compare the values at `i`. Simplify using `[Matrix.mul_apply, Matrix.mulVec, dotProduct]`.

Rewrite using `[e, hV j, Matrix.mulVec_mulVec, hWU, Matrix.one_mulVec]`. Use `⟨?_, fun i j hij => ?_⟩` and prove the remaining obligations. Use extensionality with `r j`. Establish `e1` using `congrFun (hV j) r`. Establish `e2 : (U * (Wm * V)) r j = U.mulVec (fun i => (Wm * V) i j) r`.

Simplify using `[Matrix.mul_apply, Matrix.mulVec, dotProduct]`. Rewrite using `[e2, hc j]`. Conclude with `e1`. Conclude with `(congrFun (hc j) i).trans (ha j i hij)`.
-/
theorem tri_of_cols {L : Type} [CommRing L] {n m : ℕ} (U : Matrix (Fin n) (Fin m) L) (Wm : Matrix (Fin m) (Fin n) L)
    (hWU : Wm * U = 1) (V : Matrix (Fin n) (Fin m) L)
    (h : ∀ j, ∃ a : Fin m → L, (∀ i, j < i → a i = 0) ∧ (fun r => V r j) = U.mulVec a) :
    V = U * (Wm * V) ∧ ∀ i j, j < i → (Wm * V) i j = 0 := by
  choose a ha hV using h
  have hc : ∀ j, (fun i => (Wm * V) i j) = a j := fun j => by
    have e : (fun i => (Wm * V) i j) = Wm.mulVec (fun r => V r j) := by
      funext i; simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]
    rw [e, hV j, Matrix.mulVec_mulVec, hWU, Matrix.one_mulVec]
  refine ⟨?_, fun i j hij => ?_⟩
  · ext r j
    have e1 := congrFun (hV j) r
    have e2 : (U * (Wm * V)) r j = U.mulVec (fun i => (Wm * V) i j) r := by
      simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]
    rw [e2, hc j]
    exact e1
  · exact (congrFun (hc j) i).trans (ha j i hij)

/- English proof (translation)
The claim follows from `(Spec.map_comp _ _).symm`.
-/
theorem spMap_comp_spMap {R S T : Type} [CommRing R] [CommRing S] [CommRing T] (f : R →+* S) (g : S →+* T) :
    spMap g ≫ spMap f = spMap (g.comp f) := (Spec.map_comp _ _).symm

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} {p : Proj (RingHom.id c.F)} {A : Atlas Y p}
  {Z : Scheme.{0}} {π : Z ⟶ Y.X} {g : ∀ en : En Dw.mult, Z ⟶ PSpace c.F (plN A.N en.1)}
  {κ : ∀ b, Pm Dw.mult → (Sp (CR Dw.mult (A.V b)) ⟶ Z)} [∀ b w, IsOpenImmersion (κ b w)]

/- English proof (translation)
Use `conv_lhs => rw [← eq_spMap_ev k z hz]`. Rewrite using `[Category.assoc, hZ.plk.base, cbase, ← Category.assoc, spMap_comp_spMap]`. Both sides reduce to the same expression.
-/
theorem comp_base (hZ : Cells A π g κ) (k : A.B × Pm Dw.mult) {L : Type} [CommRing L] (z : Sp L ⟶ Z)
    (hz : ⊤ ≤ z ⁻¹ᵁ (κ k.1 k.2).opensRange) :
    z ≫ π = spMap (((ev z _ hz).comp (cellθ κ k).toRingHom).comp (cC A k.1)) ≫ tau (A.V k.1).2 := by
  conv_lhs => rw [← eq_spMap_ev k z hz]
  rw [Category.assoc, hZ.plk.base, cbase, ← Category.assoc, spMap_comp_spMap]
  rfl

/- English proof (translation)
Rewrite using `[comp_base hZ k z hz]`. Conclude with `le_preimage_comp _ (tau_le _ le_rfl)`.
-/
theorem le_comp_base (hZ : Cells A π g κ) (k : A.B × Pm Dw.mult) {L : Type} [CommRing L] (z : Sp L ⟶ Z)
    (hz : ⊤ ≤ z ⁻¹ᵁ (κ k.1 k.2).opensRange) : ⊤ ≤ (z ≫ π) ⁻¹ᵁ (A.V k.1).1 := by
  rw [comp_base hZ k z hz]
  exact le_preimage_comp _ (tau_le _ le_rfl)

/- English proof (translation)
Rewrite using `[ev_congr (comp_base hZ k z hz) _ h (by rw [← comp_base hZ k z hz]; exact h)]`. Conclude with `ev_spMap_tau _ _ _`.
-/
theorem ev_comp_base (hZ : Cells A π g κ) (k : A.B × Pm Dw.mult) {L : Type} [CommRing L] (z : Sp L ⟶ Z)
    (hz : ⊤ ≤ z ⁻¹ᵁ (κ k.1 k.2).opensRange) (h : ⊤ ≤ (z ≫ π) ⁻¹ᵁ (A.V k.1).1) :
    ev (z ≫ π) _ h = ((ev z _ hz).comp (cellθ κ k).toRingHom).comp (cC A k.1) := by
  rw [ev_congr (comp_base hZ k z hz) _ h (by rw [← comp_base hZ k z hz]; exact h)]
  exact ev_spMap_tau _ _ _

/- English proof (translation)
Introduce and unpack `rfl`. Establish `h2 : (1 : L) ∈ Ideal.span (Set.range (0 : ι → L))` using `h ▸ Submodule.mem_top`. Take `⟨c, hc⟩` from `Ideal.mem_span_range_iff_exists_fun.1 h2`. Simplify using `at hc`.
-/
theorem ne_zero_of_span_eq_top {L ι : Type} [Field L] [Fintype ι] {v : ι → L} (h : Ideal.span (Set.range v) = ⊤) :
    v ≠ 0 := by
  rintro rfl
  have h2 : (1 : L) ∈ Ideal.span (Set.range (0 : ι → L)) := h ▸ Submodule.mem_top
  obtain ⟨c, hc⟩ := Ideal.mem_span_range_iff_exists_fun.1 h2
  simp at hc

/- English proof (translation)
Establish `hx` using `le_comp_base hZ k z hz`. Establish `hx'` using `le_comp_base hZ k' z hz'`. Establish `ex` using `ev_comp_base hZ k z hz hx`. Establish `ex'` using `ev_comp_base hZ k' z hz' hx'`. Establish `ez` using `eq_spMap_ev k z hz`.

Establish `ez'` using `eq_spMap_ev k' z hz'`. Take `⟨a0, ha0⟩` from `A.tw L (z ≫ π) k'.1 k.1 hx' hx hM`. Rewrite `ha0` using `[ex, ex']`. Generalize the expression as in `(chg (A.k k.1).M.toMChart (A.k k'.1).M.toMChart).map (ev (z ≫ π) _ hM) = Chx at ha0 ⊢`. Generalize the expression as in `(ev z _ hz).comp (cellθ κ k).toRingHom = ψ at ez ha0 ⊢`.

Generalize the expression as in `(ev z _ hz').comp (cellθ κ k').toRingHom = ψ' at ez' ha0 ⊢`. Establish `hj : j.1 + 1 ≤ Dw.mult σ` using `j.2`. Take `⟨hu, hp⟩` from `hZ.plk.plk k.1 k.2 (stdEn σ (j.1 + 1) hj)`. Take `⟨hu', hp'⟩` from `hZ.plk.plk k'.1 k'.2 (stdEn σ (j.1 + 1) hj)`. Establish `e1 : z ≫ g (stdEn σ (j.1 + 1) hj) = pt (ψ.comp ((MvPolynomial.C).comp ((A.alpha k.1).comp (RingHom.id c.F)))) (ψ ∘ plk (uvec (A.cv k.1) k.2) (std σ (j.1 + 1) hj)) (span_range_comp_eq_top _ hu ψ)`.

Rewrite using `[← ez, Category.assoc, hp, spMap_pt]`. Establish `e2 : z ≫ g (stdEn σ (j.1 + 1) hj) = pt (ψ'.comp ((MvPolynomial.C).comp ((A.alpha k'.1).comp (RingHom.id c.F)))) (ψ' ∘ plk (uvec (A.cv k'.1) k'.2) (std σ (j.1 + 1) hj)) (span_range_comp_eq_top _ hu' ψ')`. Rewrite using `[← ez', Category.assoc, hp', spMap_pt]`. Establish `ec : ψ.comp ((MvPolynomial.C).comp ((A.alpha k.1).comp (RingHom.id c.F))) = ψ'.comp ((MvPolynomial.C).comp ((A.alpha k'.1).comp (RingHom.id c.F)))`. Use `congrArg (· ≫ PSpace.str c.F _) (e1.symm.trans e2)` as an intermediate fact.

Simplify using `only [pt_str] at this`. Conclude with `congrArg CommRingCat.Hom.hom (Spec.map_injective this)`. Take `⟨u, hu2⟩` from `(pt_eq_pt_iff _ (span_range_comp_eq_top _ hu ψ) (span_range_comp_eq_top _ hu' ψ')).1 (e1.symm.trans (e2.trans (congrArg (fun c => pt c _ _) ec.symm)))`. Set `cv : Fin (j.1 + 1) → Fin (A.N + 1) → L` to `fun l => ψ ∘ uvec (A.cv k.1) k.2 (std σ (j.1 + 1) hj l)`. Set `cv' : Fin (j.1 + 1) → Fin (A.N + 1) → L` to `fun l => ψ' ∘ uvec (A.cv k'.1) k'.2 (std σ (j.1 + 1) hj l)`.

Establish `hpl : plk cv' id = (u : L) • plk cv id`. Use `hu2` as an intermediate fact. Rewrite `this` using `[map_plk, map_plk, Units.smul_def]`. Conclude with `this`. Establish `h0 : plk cv' id ≠ 0` using `fun h => ne_zero_of_span_eq_top (span_range_comp_eq_top _ hu' ψ') (by rw [map_plk]; exact h)`.

Establish `hmem` using `mem_span_of_plk_eq_smul L A.N (j.1 + 1) cv cv' u h0 hpl (Fin.last j.1)`. Take `⟨f, hf⟩` from `(Submodule.mem_span_range_iff_exists_fun L).1 hmem`. Establish `hcol : ∀ (b : A.B) (w : Pm Dw.mult) (φ : CR Dw.mult (A.V b) →+* L) (i : Fin (Dw.mult σ)), (fun r => φ (uvec (A.cv b) w ⟨σ, i⟩ r)) = ((A.A b).map (φ.comp (cC A b))).mulVec (((uC A b w σ).map φ).mulVec (Pi.single i 1))`. Introduce `b w φ i`. Use function extensionality and compare the values at `r`.

Rewrite using `[uvec_cv, Matrix.mulVec_single_one]`. Simplify using `[Matrix.mul_apply, Matrix.mulVec, dotProduct, map_sum]`. Set `av : Fin (Dw.mult σ) → L` to `∑ l, f l • Pi.single (Fin.castLE hj l) 1`. Establish `hq : (fun s => ψ' (uC A k'.1 k'.2 σ s j)) = ((uC A k'.1 k'.2 σ).map ψ').mulVec (Pi.single j 1)`. Use function extensionality and compare the values at `s`.

Rewrite using `[Matrix.mulVec_single_one]`. Both sides reduce to the same expression. Establish `hL : ∑ l, f l • cv l = ((A.A k.1).map (ψ.comp (cC A k.1))).mulVec (((uC A k.1 k.2 σ).map ψ).mulVec av)`. Simplify using `only [cv, av, Matrix.mulVec_sum, Matrix.mulVec_smul]`. Use `Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations.

Conclude with `congrArg _ (hcol k.1 k.2 ψ (Fin.castLE hj l))`. Establish `hR : cv' (Fin.last j.1) = (a0 : L) • ((A.A k.1).map (ψ.comp (cC A k.1))).mulVec (Chx.mulVec (fun s => ψ' (uC A k'.1 k'.2 σ s j)))`. Establish `e : Fin.castLE hj (Fin.last j.1) = j` using `Fin.ext rfl`. Use `hcol k'.1 k'.2 ψ' j` as an intermediate fact. Rewrite `this` using `[← hq, ha0, Matrix.smul_mulVec, ← Matrix.mulVec_mulVec]`.

Simplify using `only [cv', std, e]`. Conclude with `this`. Establish `hCA : (A.C k.1).map (ψ.comp (cC A k.1)) * (A.A k.1).map (ψ.comp (cC A k.1)) = 1`. Rewrite using `[← Matrix.map_mul, A.CA, Matrix.map_one _ (map_zero _) (map_one _)]`. Establish `hC : ∀ v, ((A.C k.1).map (ψ.comp (cC A k.1))).mulVec (((A.A k.1).map (ψ.comp (cC A k.1))).mulVec v) = v` using `fun v => by rw [Matrix.mulVec_mulVec, hCA, Matrix.one_mulVec]`.

Establish `key` using `congrArg ((A.C k.1).map (ψ.comp (cC A k.1))).mulVec (hf.trans hR)`. Rewrite `key` using `[hL, Matrix.mulVec_smul, hC, hC]`. Use `⟨((a0⁻¹ : Lˣ) : L) • av, fun i hi => ?_, ?_⟩` and prove the remaining obligations. Simplify using `only [av, Pi.smul_apply, Finset.sum_apply, Pi.single_apply, smul_eq_mul]`. Rewrite using `[Finset.sum_eq_zero fun l _ => ?_, mul_zero]`.

Rewrite using `[if_neg, mul_zero]`. Introduce `h`. Use `congrArg Fin.val h` as an intermediate fact. Simplify using `only [Fin.coe_castLE] at this`. Use `l.2` as an intermediate fact.

Use linear arithmetic over natural numbers and integers. Rewrite using `[Matrix.mulVec_smul, key, smul_smul, Units.inv_mul, one_smul]`.
-/
theorem col_tri (hZ : Cells A π g κ) (k k' : A.B × Pm Dw.mult) (σ : E →+* ℂ) {L : Type} [Field L] (z : Sp L ⟶ Z)
    (hz : ⊤ ≤ z ⁻¹ᵁ (κ k.1 k.2).opensRange) (hz' : ⊤ ≤ z ⁻¹ᵁ (κ k'.1 k'.2).opensRange)
    (hM : ⊤ ≤ (z ≫ π) ⁻¹ᵁ ((A.k k.1).M.U ⊓ (A.k k'.1).M.U)) (j : Fin (Dw.mult σ)) :
    ∃ a : Fin (Dw.mult σ) → L, (∀ i, j < i → a i = 0) ∧
      ((chg (A.k k.1).M.toMChart (A.k k'.1).M.toMChart).map (ev (z ≫ π) _ hM)).mulVec
        (fun s => ((ev z _ hz').comp (cellθ κ k').toRingHom) (uC A k'.1 k'.2 σ s j)) =
      ((uC A k.1 k.2 σ).map ((ev z _ hz).comp (cellθ κ k).toRingHom)).mulVec a := by
  classical
  have hx := le_comp_base hZ k z hz
  have hx' := le_comp_base hZ k' z hz'
  have ex := ev_comp_base hZ k z hz hx
  have ex' := ev_comp_base hZ k' z hz' hx'
  have ez := eq_spMap_ev k z hz
  have ez' := eq_spMap_ev k' z hz'
  obtain ⟨a0, ha0⟩ := A.tw L (z ≫ π) k'.1 k.1 hx' hx hM
  rw [ex, ex'] at ha0
  generalize (chg (A.k k.1).M.toMChart (A.k k'.1).M.toMChart).map (ev (z ≫ π) _ hM) = Chx at ha0 ⊢
  generalize (ev z _ hz).comp (cellθ κ k).toRingHom = ψ at ez ha0 ⊢
  generalize (ev z _ hz').comp (cellθ κ k').toRingHom = ψ' at ez' ha0 ⊢
  have hj : j.1 + 1 ≤ Dw.mult σ := j.2
  obtain ⟨hu, hp⟩ := hZ.plk.plk k.1 k.2 (stdEn σ (j.1 + 1) hj)
  obtain ⟨hu', hp'⟩ := hZ.plk.plk k'.1 k'.2 (stdEn σ (j.1 + 1) hj)
  have e1 : z ≫ g (stdEn σ (j.1 + 1) hj) = pt (ψ.comp ((MvPolynomial.C).comp ((A.alpha k.1).comp (RingHom.id c.F))))
      (ψ ∘ plk (uvec (A.cv k.1) k.2) (std σ (j.1 + 1) hj)) (span_range_comp_eq_top _ hu ψ) := by
    rw [← ez, Category.assoc, hp, spMap_pt]
  have e2 : z ≫ g (stdEn σ (j.1 + 1) hj) = pt (ψ'.comp ((MvPolynomial.C).comp ((A.alpha k'.1).comp (RingHom.id c.F))))
      (ψ' ∘ plk (uvec (A.cv k'.1) k'.2) (std σ (j.1 + 1) hj)) (span_range_comp_eq_top _ hu' ψ') := by
    rw [← ez', Category.assoc, hp', spMap_pt]
  have ec : ψ.comp ((MvPolynomial.C).comp ((A.alpha k.1).comp (RingHom.id c.F))) =
      ψ'.comp ((MvPolynomial.C).comp ((A.alpha k'.1).comp (RingHom.id c.F))) := by
    have := congrArg (· ≫ PSpace.str c.F _) (e1.symm.trans e2)
    simp only [pt_str] at this
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective this)
  obtain ⟨u, hu2⟩ := (pt_eq_pt_iff _ (span_range_comp_eq_top _ hu ψ) (span_range_comp_eq_top _ hu' ψ')).1
    (e1.symm.trans (e2.trans (congrArg (fun c => pt c _ _) ec.symm)))
  let cv : Fin (j.1 + 1) → Fin (A.N + 1) → L := fun l => ψ ∘ uvec (A.cv k.1) k.2 (std σ (j.1 + 1) hj l)
  let cv' : Fin (j.1 + 1) → Fin (A.N + 1) → L := fun l => ψ' ∘ uvec (A.cv k'.1) k'.2 (std σ (j.1 + 1) hj l)
  have hpl : plk cv' id = (u : L) • plk cv id := by
    have := hu2
    rw [map_plk, map_plk, Units.smul_def] at this
    exact this
  have h0 : plk cv' id ≠ 0 := fun h =>
    ne_zero_of_span_eq_top (span_range_comp_eq_top _ hu' ψ') (by rw [map_plk]; exact h)
  have hmem := mem_span_of_plk_eq_smul L A.N (j.1 + 1) cv cv' u h0 hpl (Fin.last j.1)
  obtain ⟨f, hf⟩ := (Submodule.mem_span_range_iff_exists_fun L).1 hmem
  have hcol : ∀ (b : A.B) (w : Pm Dw.mult) (φ : CR Dw.mult (A.V b) →+* L) (i : Fin (Dw.mult σ)),
      (fun r => φ (uvec (A.cv b) w ⟨σ, i⟩ r)) =
        ((A.A b).map (φ.comp (cC A b))).mulVec (((uC A b w σ).map φ).mulVec (Pi.single i 1)) := by
    intro b w φ i
    funext r
    rw [uvec_cv, Matrix.mulVec_single_one]
    simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, map_sum]
  let av : Fin (Dw.mult σ) → L := ∑ l, f l • Pi.single (Fin.castLE hj l) 1
  have hq : (fun s => ψ' (uC A k'.1 k'.2 σ s j)) = ((uC A k'.1 k'.2 σ).map ψ').mulVec (Pi.single j 1) := by
    funext s
    rw [Matrix.mulVec_single_one]
    rfl
  have hL : ∑ l, f l • cv l = ((A.A k.1).map (ψ.comp (cC A k.1))).mulVec (((uC A k.1 k.2 σ).map ψ).mulVec av) := by
    simp only [cv, av, Matrix.mulVec_sum, Matrix.mulVec_smul]
    refine Finset.sum_congr rfl fun l _ => ?_
    exact congrArg _ (hcol k.1 k.2 ψ (Fin.castLE hj l))
  have hR : cv' (Fin.last j.1) = (a0 : L) • ((A.A k.1).map (ψ.comp (cC A k.1))).mulVec
      (Chx.mulVec (fun s => ψ' (uC A k'.1 k'.2 σ s j))) := by
    have e : Fin.castLE hj (Fin.last j.1) = j := Fin.ext rfl
    have := hcol k'.1 k'.2 ψ' j
    rw [← hq, ha0, Matrix.smul_mulVec, ← Matrix.mulVec_mulVec] at this
    simp only [cv', std, e]
    exact this
  have hCA : (A.C k.1).map (ψ.comp (cC A k.1)) * (A.A k.1).map (ψ.comp (cC A k.1)) = 1 := by
    rw [← Matrix.map_mul, A.CA, Matrix.map_one _ (map_zero _) (map_one _)]
  have hC : ∀ v, ((A.C k.1).map (ψ.comp (cC A k.1))).mulVec (((A.A k.1).map (ψ.comp (cC A k.1))).mulVec v) = v :=
    fun v => by rw [Matrix.mulVec_mulVec, hCA, Matrix.one_mulVec]
  have key := congrArg ((A.C k.1).map (ψ.comp (cC A k.1))).mulVec (hf.trans hR)
  rw [hL, Matrix.mulVec_smul, hC, hC] at key
  refine ⟨((a0⁻¹ : Lˣ) : L) • av, fun i hi => ?_, ?_⟩
  · simp only [av, Pi.smul_apply, Finset.sum_apply, Pi.single_apply, smul_eq_mul]
    rw [Finset.sum_eq_zero fun l _ => ?_, mul_zero]
    rw [if_neg, mul_zero]
    intro h
    have := congrArg Fin.val h
    simp only [Fin.coe_castLE] at this
    have := l.2
    omega
  · rw [Matrix.mulVec_smul, key, smul_smul, Units.inv_mul, one_smul]

/- English proof (translation)
Establish `: ∀ x : Z, _root_.IsReduced (Z.presheaf.stalk x)` using `fun x => by`. Use `(hZ.normal x).1` as an intermediate fact. Use `infer_instance`. Conclude with `isReduced_of_isReduced_stalk _`.
-/
theorem isReduced_of_cells (hZ : Cells A π g κ) : IsReduced Z := by
  have : ∀ x : Z, _root_.IsReduced (Z.presheaf.stalk x) := fun x => by
    have := (hZ.normal x).1
    infer_instance
  exact isReduced_of_isReduced_stalk _

/- English proof (translation)
Use `haveI := isReduced_of_cells hZ`. Introduce `k k' σ`. Establish `hle : (κ k.1 k.2).opensRange ⊓ (κ k'.1 k'.2).opensRange ≤ π ⁻¹ᵁ ((A.k k.1).M.U ⊓ (A.k k'.1).M.U)` using `inf_le_inf (cell_le hZ k) (cell_le hZ k')`. Set `Cm` to `(chg (A.k k.1).M.toMChart (A.k k'.1).M.toMChart).map (π.appLE ((A.k k.1).M.U ⊓ (A.k k'.1).M.U) ((κ k.1 k.2).opensRange ⊓ (κ k'.1 k'.2).opensRange) hle).hom`. Set `U'` to `((uC A k'.1 k'.2 σ).map (cellθ κ k')).map (resG Z (inf_le_right : (κ k.1 k.2).opensRange ⊓ (κ k'.1 k'.2).opensRange ≤ _))`.

Set `U` to `((uC A k.1 k.2 σ).map (cellθ κ k)).map (resG Z (inf_le_left : (κ k.1 k.2).opensRange ⊓ (κ k'.1 k'.2).opensRange ≤ _))`. Set `Wm` to `((wC A k.1 k.2 σ).map (cellθ κ k)).map (resG Z (inf_le_left : (κ k.1 k.2).opensRange ⊓ (κ k'.1 k'.2).opensRange ≤ _))`. Establish `hWU : Wm * U = 1`. Simplify using `only [Wm, U]`. Rewrite using `[← Matrix.map_mul, ← Matrix.map_mul, wC_mul_uC, Matrix.map_one _ (map_zero _) (map_one _), Matrix.map_one _ (map_zero _) (map_one _)]`.

Establish `key : ∀ (L : Type) [Field L] (z : Sp L ⟶ Z) (hz : ⊤ ≤ z ⁻¹ᵁ ((κ k.1 k.2).opensRange ⊓ (κ k'.1 k'.2).opensRange)), (Cm * U').map (ev z _ hz) = U.map (ev z _ hz) * (Wm * (Cm * U')).map (ev z _ hz) ∧ ∀ i j, j < i → (Wm * (Cm * U')).map (ev z _ hz) i j = 0`. Introduce `L _ z hz`. Establish `hz1` using `le_preimage_mono inf_le_left hz`. Establish `hz2` using `le_preimage_mono inf_le_right hz`. Establish `hM` using `le_preimage_map π hle hz`.

Establish `eC : Cm.map (ev z _ hz) = (chg (A.k k.1).M.toMChart (A.k k'.1).M.toMChart).map (ev (z ≫ π) _ hM)`. Use extensionality with `r s`. Conclude with `ev_appLE z π hle hz hM _`. Establish `eU : U.map (ev z _ hz) = (uC A k.1 k.2 σ).map ((ev z _ hz1).comp (cellθ κ k).toRingHom)`. Use extensionality with `r s`.

Conclude with `ev_res z _ hz hz1 _`. Establish `eU' : U'.map (ev z _ hz) = (uC A k'.1 k'.2 σ).map ((ev z _ hz2).comp (cellθ κ k').toRingHom)`. Use extensionality with `r s`. Conclude with `ev_res z _ hz hz2 _`. Establish `h` using `tri_of_cols (U.map (ev z _ hz)) (Wm.map (ev z _ hz)) (by rw [← Matrix.map_mul, hWU, Matrix.map_one _ (map_zero _) (map_one _)]) ((Cm * U').map (ev z _ hz)) (fun j => by`.

Take `⟨a, ha, e⟩` from `col_tri hZ k k' σ z hz1 hz2 hM j`. Use `⟨a, ha, ?_⟩` and prove the remaining obligations. Rewrite using `[eU, ← e, Matrix.map_mul, eC, eU']`. Use function extensionality and compare the values at `r`. Simplify using `[Matrix.mul_apply, Matrix.mulVec, dotProduct])`.

Rewrite using `[show (Wm * (Cm * U')).map (ev z _ hz) = Wm.map (ev z _ hz) * (Cm * U').map (ev z _ hz) from Matrix.map_mul]`. Conclude with `h`. Use `⟨Wm * (Cm * U'), fun i j hij => ext_ev_field fun L _ z hz => ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[map_zero]`. Conclude with `(key L z hz).2 i j hij`.

Use extensionality with `r s`. Use `ext_ev_field fun L _ z hz => ?_` and prove the remaining obligations. Use `congrFun (congrFun (key L z hz).1 r) s` as an intermediate fact. Rewrite `this` using `[← Matrix.map_mul]`. Conclude with `this`.
-/
theorem flagCells_frames_triangular_common (hZ : Cells A π g κ) : FlagCellFrameChangeTriangular hZ := by
  haveI := isReduced_of_cells hZ
  intro k k' σ
  have hle : (κ k.1 k.2).opensRange ⊓ (κ k'.1 k'.2).opensRange ≤ π ⁻¹ᵁ ((A.k k.1).M.U ⊓ (A.k k'.1).M.U) :=
    inf_le_inf (cell_le hZ k) (cell_le hZ k')
  let Cm := (chg (A.k k.1).M.toMChart (A.k k'.1).M.toMChart).map
    (π.appLE ((A.k k.1).M.U ⊓ (A.k k'.1).M.U) ((κ k.1 k.2).opensRange ⊓ (κ k'.1 k'.2).opensRange) hle).hom
  let U' := ((uC A k'.1 k'.2 σ).map (cellθ κ k')).map (resG Z (inf_le_right :
    (κ k.1 k.2).opensRange ⊓ (κ k'.1 k'.2).opensRange ≤ _))
  let U := ((uC A k.1 k.2 σ).map (cellθ κ k)).map (resG Z (inf_le_left :
    (κ k.1 k.2).opensRange ⊓ (κ k'.1 k'.2).opensRange ≤ _))
  let Wm := ((wC A k.1 k.2 σ).map (cellθ κ k)).map (resG Z (inf_le_left :
    (κ k.1 k.2).opensRange ⊓ (κ k'.1 k'.2).opensRange ≤ _))
  have hWU : Wm * U = 1 := by
    simp only [Wm, U]
    rw [← Matrix.map_mul, ← Matrix.map_mul, wC_mul_uC, Matrix.map_one _ (map_zero _) (map_one _),
      Matrix.map_one _ (map_zero _) (map_one _)]
  have key : ∀ (L : Type) [Field L] (z : Sp L ⟶ Z)
      (hz : ⊤ ≤ z ⁻¹ᵁ ((κ k.1 k.2).opensRange ⊓ (κ k'.1 k'.2).opensRange)),
      (Cm * U').map (ev z _ hz) = U.map (ev z _ hz) * (Wm * (Cm * U')).map (ev z _ hz) ∧
        ∀ i j, j < i → (Wm * (Cm * U')).map (ev z _ hz) i j = 0 := by
    intro L _ z hz
    have hz1 := le_preimage_mono inf_le_left hz
    have hz2 := le_preimage_mono inf_le_right hz
    have hM := le_preimage_map π hle hz
    have eC : Cm.map (ev z _ hz) = (chg (A.k k.1).M.toMChart (A.k k'.1).M.toMChart).map (ev (z ≫ π) _ hM) := by
      ext r s
      exact ev_appLE z π hle hz hM _
    have eU : U.map (ev z _ hz) = (uC A k.1 k.2 σ).map ((ev z _ hz1).comp (cellθ κ k).toRingHom) := by
      ext r s
      exact ev_res z _ hz hz1 _
    have eU' : U'.map (ev z _ hz) = (uC A k'.1 k'.2 σ).map ((ev z _ hz2).comp (cellθ κ k').toRingHom) := by
      ext r s
      exact ev_res z _ hz hz2 _
    have h := tri_of_cols (U.map (ev z _ hz)) (Wm.map (ev z _ hz))
      (by rw [← Matrix.map_mul, hWU, Matrix.map_one _ (map_zero _) (map_one _)]) ((Cm * U').map (ev z _ hz))
      (fun j => by
        obtain ⟨a, ha, e⟩ := col_tri hZ k k' σ z hz1 hz2 hM j
        refine ⟨a, ha, ?_⟩
        rw [eU, ← e, Matrix.map_mul, eC, eU']
        funext r
        simp [Matrix.mul_apply, Matrix.mulVec, dotProduct])
    rw [show (Wm * (Cm * U')).map (ev z _ hz) = Wm.map (ev z _ hz) * (Cm * U').map (ev z _ hz) from Matrix.map_mul]
    exact h
  refine ⟨Wm * (Cm * U'), fun i j hij => ext_ev_field fun L _ z hz => ?_, ?_⟩
  · rw [map_zero]
    exact (key L z hz).2 i j hij
  · ext r s
    refine ext_ev_field fun L _ z hz => ?_
    have := congrFun (congrFun (key L z hz).1 r) s
    rw [← Matrix.map_mul] at this
    exact this

end GlobalTheory.FlagMod.FieldFlag

open AlgebraicGeometry CategoryTheory TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg GlobalTheory.FlagEmb GlobalTheory.ProjSpace GlobalTheory.FlagMod GlobalTheory.FlagMod.FieldFlag
open GlobalTheory.FlagMod.LowRank (ECh Proj str)

/- English proof (translation)
Introduce `_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hZ` and use `GlobalTheory.FlagMod.FieldFlag.flagCells_frames_triangular_common hZ`.
-/
theorem GlobalTheory.FlagMod.FieldFlag.flagCells_frames_triangular : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (p : Proj (RingHom.id c.F)) (A : Atlas Y p) (Z : Scheme.{0}) (π : Z ⟶ Y.X) (g : ∀ en : En Dw.mult, Z ⟶ PSpace c.F (plN A.N en.1)) (κ : ∀ b, Pm Dw.mult → (Sp (CR Dw.mult (A.V b)) ⟶ Z)) [∀ b w, IsOpenImmersion (κ b w)] (hZ : Cells A π g κ), FlagCellFrameChangeTriangular hZ :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hZ => GlobalTheory.FlagMod.FieldFlag.flagCells_frames_triangular_common hZ
