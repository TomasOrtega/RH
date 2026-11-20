import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFrameCover
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CauchyBinetPluckerAndCellCoordinatesStatement

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.ProjSpace GlobalTheory.FlagEmb
open Formalism.MainNotions.DIV.Cons (intO)

namespace GlobalTheory.FlagEmb.CellClosed

/- English proof (translation)
Simplify using `only [spMap, ← Spec.map_comp]`. Both sides reduce to the same expression.
-/
theorem sp_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  simp only [spMap, ← Spec.map_comp]
  rfl

/- English proof (translation)
Establish `e` using `Spec.map_injective h`. Use extensionality with `a`. Conclude with `congrArg (fun t => t.hom a) e`.
-/
theorem sp_inj {A B : Type} [CommRing A] [CommRing B] {f g : A →+* B} (h : spMap f = spMap g) : f = g := by
  have e := Spec.map_injective h
  ext a
  exact congrArg (fun t => t.hom a) e

/- English proof (translation)
Assemble the required witnesses or components as `⟨(Spec.preimage f).hom, by simp [spMap]⟩`.
-/
theorem sp_surj {A B : Type} [CommRing A] [CommRing B] (f : Sp B ⟶ Sp A) : ∃ g : A →+* B, f = spMap g := ⟨(Spec.preimage f).hom, by simp [spMap]⟩

/- English proof (translation)
Establish `hb : b = b'` using `sp_inj (by rw [← pt_str b v hv, ← pt_str b' v' hv', h])`. Substitute `hb` using the available equality. Conclude with `(pt_eq_pt_iff b hv hv').1 h`.
-/
theorem unit_of_pt_eq {O A : Type} [CommRing O] [CommRing A] {N : ℕ} {b b' : O →+* A} {v v' : Fin (N + 1) → A} {hv hv'}
    (h : pt b v hv = pt b' v' hv') : ∃ u : Aˣ, v' = u • v := by
  have hb : b = b' := sp_inj (by rw [← pt_str b v hv, ← pt_str b' v' hv', h])
  subst hb
  exact (pt_eq_pt_iff b hv hv').1 h

/- English proof (translation)
Simplify using `[lform, map_prod]`.
-/
theorem map_lform {S S' : Type} [CommRing S] [CommRing S'] (φ : S →+* S') {M k : ℕ} {ι : Type}
    (D : ι → Fin (M + 1) → S) (ρ : Fin k → ι) (q) : φ (lform D ρ q) = lform (fun z => φ ∘ D z) ρ q := by
  simp [lform, map_prod]

section

variable {X : Scheme.{0}} {T : Type} {m : T → ℕ} {M : ℕ} {U : X.affineOpens} {c D : Let m → Fin (M + 1) → Γ(X, U.1)}
  {w : Pm m} {R : Type} [CommRing R]

/- English proof (translation)
Rewrite using `[map_plk]`. Use `congr 1`. Use function extensionality and compare the values at `z`. Rewrite using `[uvec, map_cellVec]`. Both sides reduce to the same expression.
-/
theorem map_uvec (ψ : CR m U →+* R) {k : ℕ} (e : Fin k → Let m) :
    ψ ∘ plk (uvec c w) e = plk (cellVec (fun z => ψ.comp MvPolynomial.C ∘ c z) w (ψ ∘ MvPolynomial.X)) e := by
  rw [map_plk]
  congr 1
  funext z
  rw [uvec, map_cellVec]
  rfl

/- English proof (translation)
Establish `hL` using `LeftInv.map (ψ.comp MvPolynomial.C) hD`. Establish `key` using `(GlobalTheory.T.cauchyBinet_plucker_and_cellCoordinates.2 T m R M _ _ w (ψ ∘ MvPolynomial.X) hL).1 k e he`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun q _ => ?_` and prove the remaining obligations.

Rewrite using `[Pi.smul_apply, Units.smul_def, smul_eq_mul, map_uvec, map_lform]`. Expand and normalize the polynomial expressions, which then agree. Use `_ = u := by rw [key, mul_one]`.
-/
theorem lead_eq (hD : LeftInv D c) (ψ : CR m U →+* R) {k : ℕ} {e : Fin k → Let m} (he : Down e) (u : Rˣ) :
    ∑ q, ψ.comp MvPolynomial.C (lform D (wLet w ∘ e) q) * (u • ψ ∘ plk (uvec c w) e) q = u := by
  have hL := LeftInv.map (ψ.comp MvPolynomial.C) hD
  have key := (GlobalTheory.T.cauchyBinet_plucker_and_cellCoordinates.2 T m R M _ _ w (ψ ∘ MvPolynomial.X) hL).1 k e he
  calc _ = (u : R) * ∑ q, lform (fun z => ψ.comp MvPolynomial.C ∘ D z) (wLet w ∘ e) q *
        plk (cellVec (fun z => ψ.comp MvPolynomial.C ∘ c z) w (ψ ∘ MvPolynomial.X)) e q := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun q _ => ?_
        rw [Pi.smul_apply, Units.smul_def, smul_eq_mul, map_uvec, map_lform]
        ring
    _ = u := by rw [key, mul_one]

def rd (w : Pm m) (x : CellVar m) : Fin (x.2.1.2 + 1) → Let m := fun l =>
  wLet w ⟨x.1, if (l : ℕ) = x.2.1.2 then x.2.1.1 else Fin.castLE (Nat.succ_le_of_lt x.2.1.2.2) l⟩

abbrev vEn (x : CellVar m) : En m := stdEn x.1 (x.2.1.2 + 1) (Nat.succ_le_of_lt x.2.1.2.2)

/- English proof (translation)
Take `⟨τ, ⟨⟨i, j⟩, hij⟩⟩` from `x`. Establish `hL` using `LeftInv.map (ψ.comp MvPolynomial.C) hD`. Establish `key` using `(GlobalTheory.T.cauchyBinet_plucker_and_cellCoordinates.2 T m R M _ _ w (ψ ∘ MvPolynomial.X) hL).2 τ i j hij`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Finset.mul_sum]`.

Use `Finset.sum_congr rfl fun q _ => ?_` and prove the remaining obligations. Rewrite using `[Pi.smul_apply, Units.smul_def, smul_eq_mul, map_uvec, map_lform]`. Expand and normalize the polynomial expressions, which then agree. Use `_ = u * ψ (MvPolynomial.X ⟨τ, ⟨(i, j), hij⟩⟩) := by`. Conclude with `congrArg ((u : R) * ·) key`.
-/
theorem read_eq (hD : LeftInv D c) (ψ : CR m U →+* R) (x : CellVar m) (u : Rˣ) :
    ∑ q, ψ.comp MvPolynomial.C (lform D (rd w x) q) * (u • ψ ∘ plk (uvec c w) (vEn x).2.1) q =
      u * ψ (MvPolynomial.X x) := by
  obtain ⟨τ, ⟨⟨i, j⟩, hij⟩⟩ := x
  have hL := LeftInv.map (ψ.comp MvPolynomial.C) hD
  have key := (GlobalTheory.T.cauchyBinet_plucker_and_cellCoordinates.2 T m R M _ _ w (ψ ∘ MvPolynomial.X) hL).2 τ i j hij
  calc _ = (u : R) * ∑ q, lform (fun z => ψ.comp MvPolynomial.C ∘ D z) (rd w ⟨τ, ⟨(i, j), hij⟩⟩) q *
        plk (cellVec (fun z => ψ.comp MvPolynomial.C ∘ c z) w (ψ ∘ MvPolynomial.X))
          (vEn (m := m) ⟨τ, ⟨(i, j), hij⟩⟩).2.1 q := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun q _ => ?_
        rw [Pi.smul_apply, Units.smul_def, smul_eq_mul, map_uvec, map_lform]
        ring
    _ = u * ψ (MvPolynomial.X ⟨τ, ⟨(i, j), hij⟩⟩) := by
        exact congrArg ((u : R) * ·) key

end

section

variable {O : Type} [CommRing O] {X : Scheme.{0}} {T : Type} {m : T → ℕ} {M : ℕ} {U : X.affineOpens}
  {c D : Let m → Fin (M + 1) → Γ(X, U.1)} {w : Pm m} {P : Scheme.{0}} {p0 : P ⟶ X}
  {p : ∀ en : En m, P ⟶ PSpace O (plN M en.1)} {h : Sp (CR m U) ⟶ P} {a : O →+* CR m U}

/- English proof (translation)
Establish `: IsOpenImmersion U.2.fromSpec` using `U.2.isOpenImmersion_fromSpec`. Establish `: Mono U.2.fromSpec` using `IsOpenImmersion.mono _`. Conclude with `sp_inj ((cancel_mono U.2.fromSpec).1 e)`.
-/
theorem over_inj {R : Type} [CommRing R] {φ φ' : Γ(X, U.1) →+* R}
    (e : spMap φ ≫ U.2.fromSpec = spMap φ' ≫ U.2.fromSpec) : φ = φ' := by
  have : IsOpenImmersion U.2.fromSpec := U.2.isOpenImmersion_fromSpec
  have : Mono U.2.fromSpec := IsOpenImmersion.mono _
  exact sp_inj ((cancel_mono U.2.fromSpec).1 e)

/- English proof (translation)
Rewrite using `[Category.assoc, hb, cbase, ← Category.assoc, sp_comp]`.
-/
theorem base_eq (hb : h ≫ p0 = cbase m U) {R : Type} [CommRing R] (ψ : CR m U →+* R) :
    (spMap ψ ≫ h) ≫ p0 = spMap (ψ.comp MvPolynomial.C) ≫ U.2.fromSpec := by
  rw [Category.assoc, hb, cbase, ← Category.assoc, sp_comp]

/- English proof (translation)
Take `⟨hu, he⟩` from `hp en`. Rewrite `e` using `[Category.assoc, he, spMap_pt]`. Conclude with `unit_of_pt_eq e`.
-/
theorem unit_of_eq (hp : ∀ en, ∃ hu, h ≫ p en = pt a (plk (uvec c w) en.2.1) hu) {R : Type} [CommRing R]
    (ψ : CR m U →+* R) (en : En m) {b : O →+* R} {v hv} (e : (spMap ψ ≫ h) ≫ p en = pt b v hv) :
    ∃ u : Rˣ, v = u • ψ ∘ plk (uvec c w) en.2.1 := by
  obtain ⟨hu, he⟩ := hp en
  rw [Category.assoc, he, spMap_pt] at e
  exact unit_of_pt_eq e

/- English proof (translation)
Introduce and unpack `_ ⟨y, rfl⟩`. Set `y' : PrimeSpectrum (CR m U)` to `y`. Set `k` to `y'.asIdeal.ResidueField`. Set `f : CR m U →+* k` to `algebraMap (CR m U) k`. Establish `hz : Set.range (spMap f ≫ h) ⊆ W`.

Use `(hW k (spMap f ≫ h)).2 ⟨f.comp MvPolynomial.C, base_eq hb f, ?_⟩` and prove the remaining obligations. Introduce `τ j hj b v hv e`. Take `⟨u, rfl⟩` from `unit_of_eq hp f _ e`. Establish `hl` using `lead_eq (w := w) hD f (down_std τ j hj) u`. Introduce `h0`.

Conclude with `u.ne_zero (hl.symm.trans h0)`. Establish `hy : (spMap f) (show Sp k from (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum k)) = y`. Apply `PrimeSpectrum.ext` to reduce the goal to its premises. Conclude with `Ideal.ker_algebraMap_residueField _`. Conclude with `hz ⟨_, by rw [Scheme.Hom.comp_apply, hy]⟩`.
-/
theorem range_le (hD : LeftInv D c) (hb : h ≫ p0 = cbase m U)
    (hp : ∀ en, ∃ hu, h ≫ p en = pt a (plk (uvec c w) en.2.1) hu) {W : P.Opens} (hW : IsCellOpen p0 p U D w W) :
    Set.range h ⊆ W := by
  rintro _ ⟨y, rfl⟩
  let y' : PrimeSpectrum (CR m U) := y
  let k := y'.asIdeal.ResidueField
  let f : CR m U →+* k := algebraMap (CR m U) k
  have hz : Set.range (spMap f ≫ h) ⊆ W := by
    refine (hW k (spMap f ≫ h)).2 ⟨f.comp MvPolynomial.C, base_eq hb f, ?_⟩
    intro τ j hj b v hv e
    obtain ⟨u, rfl⟩ := unit_of_eq hp f _ e
    have hl := lead_eq (w := w) hD f (down_std τ j hj) u
    intro h0
    exact u.ne_zero (hl.symm.trans h0)
  have hy : (spMap f) (show Sp k from (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum k)) = y := by
    apply PrimeSpectrum.ext
    exact Ideal.ker_algebraMap_residueField _
  exact hz ⟨_, by rw [Scheme.Hom.comp_apply, hy]⟩

/- English proof (translation)
Take `⟨ψ₁, rfl⟩` from `sp_surj (A := CR m U) (B := R) t₁`. Take `⟨ψ₂, rfl⟩` from `sp_surj (A := CR m U) (B := R) t₂`. Establish `hC : ψ₁.comp MvPolynomial.C = ψ₂.comp MvPolynomial.C` using `over_inj (by rw [← base_eq hb ψ₁, ← base_eq hb ψ₂, e])`. Use `congr 1`. Apply `MvPolynomial.ringHom_ext` to reduce the goal to its premises.

Introduce `r`. Conclude with `congrArg (fun f => f r) hC`. Introduce `x`. Take `⟨hu₂, he₂⟩` from `hp (vEn x)`. Establish `e₂ : (spMap ψ₁ ≫ h) ≫ p (vEn x) = pt (ψ₂.comp a) (ψ₂ ∘ plk (uvec c w) (vEn x).2.1) (span_range_comp_eq_top _ hu₂ ψ₂)`.

Rewrite using `[e, Category.assoc, he₂, spMap_pt]`. Take `⟨u, hu⟩` from `unit_of_eq hp ψ₁ (vEn x) e₂`. Establish `l₁` using `lead_eq (w := w) hD ψ₁ (vEn x).2.2 u`. Establish `l₂` using `lead_eq (w := w) hD ψ₂ (vEn x).2.2 1`. Establish `r₁` using `read_eq (w := w) hD ψ₁ x u`.

Establish `r₂` using `read_eq (w := w) hD ψ₂ x 1`. Rewrite `l₂`, `r₂` using `[one_smul, hu, ← hC]`. Establish `hu₁ : (u : R) = 1` using `l₁.symm.trans (by rw [l₂, Units.val_one])`. Establish `key` using `r₁.symm.trans r₂`. Rewrite `key` using `[hu₁, Units.val_one, one_mul, one_mul]`.

Conclude with `key`.
-/
private theorem mono_cell_lemma (hD : LeftInv D c) (hb : h ≫ p0 = cbase m U)
    (hp : ∀ en, ∃ hu, h ≫ p en = pt a (plk (uvec c w) en.2.1) hu) {R : CommRingCat}
    (t₁ t₂ : Spec R ⟶ Sp (CR m U)) (e : t₁ ≫ h = t₂ ≫ h) : t₁ = t₂ := by
  obtain ⟨ψ₁, rfl⟩ := sp_surj (A := CR m U) (B := R) t₁
  obtain ⟨ψ₂, rfl⟩ := sp_surj (A := CR m U) (B := R) t₂
  have hC : ψ₁.comp MvPolynomial.C = ψ₂.comp MvPolynomial.C :=
    over_inj (by rw [← base_eq hb ψ₁, ← base_eq hb ψ₂, e])
  congr 1
  apply MvPolynomial.ringHom_ext
  · intro r
    exact congrArg (fun f => f r) hC
  · intro x
    obtain ⟨hu₂, he₂⟩ := hp (vEn x)
    have e₂ : (spMap ψ₁ ≫ h) ≫ p (vEn x) =
        pt (ψ₂.comp a) (ψ₂ ∘ plk (uvec c w) (vEn x).2.1) (span_range_comp_eq_top _ hu₂ ψ₂) := by
      rw [e, Category.assoc, he₂, spMap_pt]
    obtain ⟨u, hu⟩ := unit_of_eq hp ψ₁ (vEn x) e₂
    have l₁ := lead_eq (w := w) hD ψ₁ (vEn x).2.2 u
    have l₂ := lead_eq (w := w) hD ψ₂ (vEn x).2.2 1
    have r₁ := read_eq (w := w) hD ψ₁ x u
    have r₂ := read_eq (w := w) hD ψ₂ x 1
    rw [one_smul, hu, ← hC] at l₂ r₂
    have hu₁ : (u : R) = 1 := l₁.symm.trans (by rw [l₂, Units.val_one])
    have key := r₁.symm.trans r₂
    rw [hu₁, Units.val_one, one_mul, one_mul] at key
    exact key

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `Z g₁ g₂ e`. Use `Z.affineCover.hom_ext _ _ fun i => ?_` and prove the remaining obligations. Conclude with `mono_cell_lemma hD hb hp _ _ ((Category.assoc _ _ _).trans ((congrArg (Z.affineCover.f i ≫ ·) e).trans (Category.assoc _ _ _).symm))`.
-/
theorem mono_cell (hD : LeftInv D c) (hb : h ≫ p0 = cbase m U)
    (hp : ∀ en, ∃ hu, h ≫ p en = pt a (plk (uvec c w) en.2.1) hu) : Mono h := by
  constructor
  intro Z g₁ g₂ e
  refine Z.affineCover.hom_ext _ _ fun i => ?_
  exact mono_cell_lemma hD hb hp _ _
    ((Category.assoc _ _ _).trans ((congrArg (Z.affineCover.f i ≫ ·) e).trans (Category.assoc _ _ _).symm))

/- English proof (translation)
Establish `: IsOpenImmersion U.2.fromSpec` using `U.2.isOpenImmersion_fromSpec`. Set `k` to `IsLocalRing.ResidueField R`. Set `π : R →+* k` to `IsLocalRing.residue R`. Establish `hzk : Set.range (spMap π ≫ z) ⊆ W` using `fun _ ⟨t, ht⟩ => hz ⟨(spMap π) t, by rw [← ht, Scheme.Hom.comp_apply]⟩`. Take `⟨φk, hφk, hmin⟩` from `(hW k (spMap π ≫ z)).1 hzk`.

Establish `hU : Set.range (z ≫ p0) ⊆ Set.range U.2.fromSpec`. Rewrite using `[U.2.range_fromSpec]`. Introduce and unpack `_ ⟨y, rfl⟩`. Establish `h0 : (z ≫ p0) (show Sp R from IsLocalRing.closedPoint R) ∈ (U.1 : Set X)`. Establish `h1 : (spMap π ≫ z ≫ p0) (show Sp k from IsLocalRing.closedPoint k) ∈ Set.range U.2.fromSpec`.

Rewrite using `[← Category.assoc, hφk, Scheme.Hom.comp_apply]`. Conclude with `⟨_, rfl⟩`. Rewrite `h1` using `[U.2.range_fromSpec, Scheme.Hom.comp_apply]`. Establish `hc : (spMap π) (show Sp k from IsLocalRing.closedPoint k) = IsLocalRing.closedPoint R` using `IsLocalRing.comap_closedPoint π`. Rewrite `h1` using `[hc]`. Then use the resulting hypothesis.

Conclude with `((IsLocalRing.specializes_closedPoint (show PrimeSpectrum R from y)).map (z ≫ p0).continuous).mem_open U.1.isOpen h0`. Take `⟨φ0, hφ0⟩` from `sp_surj (A := Γ(X, U.1)) (B := R) (IsOpenImmersion.lift U.2.fromSpec (z ≫ p0) hU)`. Establish `hz0 : z ≫ p0 = spMap φ0 ≫ U.2.fromSpec` using `by rw [← hφ0, IsOpenImmersion.lift_fac]`. Establish `hC : ψ.comp MvPolynomial.C = (algebraMap R K).comp φ0` using `over_inj (by rw [← base_eq hb ψ, e, Category.assoc, hz0, ← Category.assoc, sp_comp])`. Establish `hk : φk = π.comp φ0` using `over_inj (by rw [← hφk, Category.assoc, hz0, ← Category.assoc, sp_comp])`.

Take `⟨bO, hbO⟩` from `sp_surj (A := O) (B := R) (z ≫ p0 ≫ s)`. Establish `hpt : ∀ en, ∃ (v : Fin (plN M en.1 + 1) → R) (hv : Ideal.span (Set.range v) = ⊤), z ≫ p en = pt bO v hv` using `fun en => exists_eq_pt bO (z ≫ p en) (by rw [Category.assoc, hs, hbO])`. Use `choose V hV hzV using hpt`. Establish `key : ∀ x : CellVar m, ∃ r : R, algebraMap R K r = ψ (MvPolynomial.X x)`. Introduce `x`.

Take `⟨u, hu⟩` from `unit_of_eq hp ψ (vEn x) (b := (algebraMap R K).comp bO) (v := algebraMap R K ∘ V (vEn x)) (hv := span_range_comp_eq_top _ (hV _) _) (by rw [e, Category.assoc, hzV, spMap_pt])`. Establish `hL : algebraMap R K (∑ q, φ0 (lform D (wLet w ∘ (vEn x).2.1) q) * V (vEn x) q) = u`. Rewrite using `[map_sum, ← lead_eq (w := w) hD ψ (vEn x).2.2 u]`. Use `Finset.sum_congr rfl fun q _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul, ← hu, hC]`.

Both sides reduce to the same expression. Establish `hR : algebraMap R K (∑ q, φ0 (lform D (rd w x) q) * V (vEn x) q) = u * ψ (MvPolynomial.X x)`. Rewrite using `[map_sum, ← read_eq hD ψ x u]`. Use `Finset.sum_congr rfl fun q _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul, ← hu, hC]`.

Both sides reduce to the same expression. Establish `hne : π (∑ q, φ0 (lform D (wLet w ∘ (vEn x).2.1) q) * V (vEn x) q) ≠ 0`. Use `hmin x.1 (x.2.1.2 + 1) (Nat.succ_le_of_lt x.2.1.2.2) (π.comp bO) (π ∘ V (vEn x)) (span_range_comp_eq_top _ (hV _) π) (by rw [Category.assoc, hzV, spMap_pt])` as an intermediate fact. Rewrite `this` using `[hk]`. Rewrite using `[map_sum]`.

Simplify using `only [map_mul]`. Conclude with `this`. Take `⟨t, ht⟩` from `(IsLocalRing.residue_ne_zero_iff_isUnit _).1 hne`. Establish `ht' : algebraMap R K (t : R) = u` using `by rw [ht, hL]`. Establish `h1 : algebraMap R K (↑t⁻¹ : R) * (u : K) = 1`.

Rewrite using `[← ht', ← map_mul, Units.inv_mul, map_one]`. Use `⟨(∑ q, φ0 (lform D (rd w x) q) * V (vEn x) q) * ↑t⁻¹, ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul, hR]`. Combine the equalities or inequalities in the displayed calculation. Use `choose r hr using key`.

Establish `hχ : (algebraMap R K).comp (MvPolynomial.eval₂Hom φ0 r) = ψ`. Apply `MvPolynomial.ringHom_ext` to reduce the goal to its premises. Introduce `a`. Simplify using `only [RingHom.comp_apply, MvPolynomial.eval₂Hom_C]`. Conclude with `(congrArg (fun f => f a) hC).symm`.

Introduce `x`. Simplify using `only [RingHom.comp_apply, MvPolynomial.eval₂Hom_X']`. Conclude with `hr x`. Use `⟨MvPolynomial.eval₂Hom φ0 r, hχ, ?_⟩` and prove the remaining obligations. Establish `: IsDominant (spMap (algebraMap R K))`.

Prove the components needed by the constructor for the conclusion. Rewrite using `[DenseRange, dense_iff_closure_eq, Set.eq_univ_iff_forall]`. Introduce `y`. Establish `hg : (show Sp R from (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum R)) ∈ Set.range (spMap (algebraMap R K))` using `⟨show Sp K from (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum K), PrimeSpectrum.ext ((RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective R K))⟩`. Use `closure_mono (Set.singleton_subset_iff.2 hg) ?_` and prove the remaining obligations.

Use `show (show PrimeSpectrum R from y) ∈ closure ({⟨⊥, Ideal.isPrime_bot⟩} : Set (PrimeSpectrum R))`. Rewrite using `[PrimeSpectrum.closure_singleton, PrimeSpectrum.mem_zeroLocus]`. Introduce `a ha`. Rewrite `ha` using `[SetLike.mem_coe, Ideal.mem_bot]`. Rewrite using `[ha]`.

Conclude with `Submodule.zero_mem _`. Use `ext_of_isDominant_of_isSeparated (p0 ≫ s) ?_ (spMap (algebraMap R K)) ?_` and prove the remaining obligations. Rewrite using `[← Category.assoc, base_eq hb, MvPolynomial.eval₂Hom_comp_C, ← hz0, Category.assoc]`. Rewrite using `[← Category.assoc, sp_comp, hχ, e]`.
-/
theorem exists_lift (hD : LeftInv D c) (hb : h ≫ p0 = cbase m U)
    (hp : ∀ en, ∃ hu, h ≫ p en = pt a (plk (uvec c w) en.2.1) hu) {W : P.Opens} (hW : IsCellOpen p0 p U D w W)
    {s : X ⟶ Sp O} [IsSeparated (p0 ≫ s)] (hs : ∀ en, p en ≫ PSpace.str _ _ = p0 ≫ s)
    {R K : Type} [CommRing R] [IsLocalRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
    (z : Sp R ⟶ P) (hz : Set.range z ⊆ W) (ψ : CR m U →+* K) (e : spMap ψ ≫ h = spMap (algebraMap R K) ≫ z) :
    ∃ χ : CR m U →+* R, (algebraMap R K).comp χ = ψ ∧ spMap χ ≫ h = z := by
  classical
  have : IsOpenImmersion U.2.fromSpec := U.2.isOpenImmersion_fromSpec
  let k := IsLocalRing.ResidueField R
  let π : R →+* k := IsLocalRing.residue R
  have hzk : Set.range (spMap π ≫ z) ⊆ W := fun _ ⟨t, ht⟩ => hz ⟨(spMap π) t, by rw [← ht, Scheme.Hom.comp_apply]⟩
  obtain ⟨φk, hφk, hmin⟩ := (hW k (spMap π ≫ z)).1 hzk
  have hU : Set.range (z ≫ p0) ⊆ Set.range U.2.fromSpec := by
    rw [U.2.range_fromSpec]
    rintro _ ⟨y, rfl⟩
    have h0 : (z ≫ p0) (show Sp R from IsLocalRing.closedPoint R) ∈ (U.1 : Set X) := by
      have h1 : (spMap π ≫ z ≫ p0) (show Sp k from IsLocalRing.closedPoint k) ∈ Set.range U.2.fromSpec := by
        rw [← Category.assoc, hφk, Scheme.Hom.comp_apply]
        exact ⟨_, rfl⟩
      rw [U.2.range_fromSpec, Scheme.Hom.comp_apply] at h1
      have hc : (spMap π) (show Sp k from IsLocalRing.closedPoint k) = IsLocalRing.closedPoint R :=
        IsLocalRing.comap_closedPoint π
      rwa [hc] at h1
    exact ((IsLocalRing.specializes_closedPoint (show PrimeSpectrum R from y)).map
      (z ≫ p0).continuous).mem_open U.1.isOpen h0
  obtain ⟨φ0, hφ0⟩ := sp_surj (A := Γ(X, U.1)) (B := R) (IsOpenImmersion.lift U.2.fromSpec (z ≫ p0) hU)
  have hz0 : z ≫ p0 = spMap φ0 ≫ U.2.fromSpec := by rw [← hφ0, IsOpenImmersion.lift_fac]
  have hC : ψ.comp MvPolynomial.C = (algebraMap R K).comp φ0 :=
    over_inj (by rw [← base_eq hb ψ, e, Category.assoc, hz0, ← Category.assoc, sp_comp])
  have hk : φk = π.comp φ0 := over_inj (by rw [← hφk, Category.assoc, hz0, ← Category.assoc, sp_comp])
  obtain ⟨bO, hbO⟩ := sp_surj (A := O) (B := R) (z ≫ p0 ≫ s)
  have hpt : ∀ en, ∃ (v : Fin (plN M en.1 + 1) → R) (hv : Ideal.span (Set.range v) = ⊤), z ≫ p en = pt bO v hv :=
    fun en => exists_eq_pt bO (z ≫ p en) (by rw [Category.assoc, hs, hbO])
  choose V hV hzV using hpt
  have key : ∀ x : CellVar m, ∃ r : R, algebraMap R K r = ψ (MvPolynomial.X x) := by
    intro x
    obtain ⟨u, hu⟩ := unit_of_eq hp ψ (vEn x) (b := (algebraMap R K).comp bO) (v := algebraMap R K ∘ V (vEn x))
      (hv := span_range_comp_eq_top _ (hV _) _) (by rw [e, Category.assoc, hzV, spMap_pt])
    have hL : algebraMap R K (∑ q, φ0 (lform D (wLet w ∘ (vEn x).2.1) q) * V (vEn x) q) = u := by
      rw [map_sum, ← lead_eq (w := w) hD ψ (vEn x).2.2 u]
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [map_mul, ← hu, hC]
      rfl
    have hR : algebraMap R K (∑ q, φ0 (lform D (rd w x) q) * V (vEn x) q) = u * ψ (MvPolynomial.X x) := by
      rw [map_sum, ← read_eq hD ψ x u]
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [map_mul, ← hu, hC]
      rfl
    have hne : π (∑ q, φ0 (lform D (wLet w ∘ (vEn x).2.1) q) * V (vEn x) q) ≠ 0 := by
      have := hmin x.1 (x.2.1.2 + 1) (Nat.succ_le_of_lt x.2.1.2.2) (π.comp bO) (π ∘ V (vEn x))
        (span_range_comp_eq_top _ (hV _) π) (by rw [Category.assoc, hzV, spMap_pt])
      rw [hk] at this
      rw [map_sum]
      simp only [map_mul]
      exact this
    obtain ⟨t, ht⟩ := (IsLocalRing.residue_ne_zero_iff_isUnit _).1 hne
    have ht' : algebraMap R K (t : R) = u := by rw [ht, hL]
    have h1 : algebraMap R K (↑t⁻¹ : R) * (u : K) = 1 := by
      rw [← ht', ← map_mul, Units.inv_mul, map_one]
    refine ⟨(∑ q, φ0 (lform D (rd w x) q) * V (vEn x) q) * ↑t⁻¹, ?_⟩
    rw [map_mul, hR]
    calc (u : K) * ψ (MvPolynomial.X x) * algebraMap R K ↑t⁻¹ =
        (algebraMap R K ↑t⁻¹ * u) * ψ (MvPolynomial.X x) := by ring
      _ = ψ (MvPolynomial.X x) := by rw [h1, one_mul]
  choose r hr using key
  have hχ : (algebraMap R K).comp (MvPolynomial.eval₂Hom φ0 r) = ψ := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp only [RingHom.comp_apply, MvPolynomial.eval₂Hom_C]
      exact (congrArg (fun f => f a) hC).symm
    · intro x
      simp only [RingHom.comp_apply, MvPolynomial.eval₂Hom_X']
      exact hr x
  refine ⟨MvPolynomial.eval₂Hom φ0 r, hχ, ?_⟩
  have : IsDominant (spMap (algebraMap R K)) := by
    constructor
    rw [DenseRange, dense_iff_closure_eq, Set.eq_univ_iff_forall]
    intro y
    have hg : (show Sp R from (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum R)) ∈ Set.range (spMap (algebraMap R K)) :=
      ⟨show Sp K from (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum K),
        PrimeSpectrum.ext ((RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective R K))⟩
    refine closure_mono (Set.singleton_subset_iff.2 hg) ?_
    show (show PrimeSpectrum R from y) ∈ closure ({⟨⊥, Ideal.isPrime_bot⟩} : Set (PrimeSpectrum R))
    rw [PrimeSpectrum.closure_singleton, PrimeSpectrum.mem_zeroLocus]
    intro a ha
    rw [SetLike.mem_coe, Ideal.mem_bot] at ha
    rw [ha]
    exact Submodule.zero_mem _
  refine ext_of_isDominant_of_isSeparated (p0 ≫ s) ?_ (spMap (algebraMap R K)) ?_
  · rw [← Category.assoc, base_eq hb, MvPolynomial.eval₂Hom_comp_C, ← hz0, Category.assoc]
  · rw [← Category.assoc, sp_comp, hχ, e]

/- English proof (translation)
Establish `hr : Set.range h ⊆ Set.range W.ι`. Rewrite using `[Scheme.Opens.range_ι]`. Conclude with `range_le hD hb hp hW`. Set `h'` to `IsOpenImmersion.lift W.ι h hr`. Establish `hfac : h' ≫ W.ι = h` using `IsOpenImmersion.lift_fac _ _ _`.

Use `⟨h', hfac, ?_⟩` and prove the remaining obligations. Establish `: Mono h` using `mono_cell hD hb hp`. Establish `: Mono h'` using `mono_of_mono_fac hfac`. Establish `: IsAffine (Sp (CR m U))` using `inferInstanceAs (IsAffine (Spec _))`. Establish `: IsAffine (Sp O)` using `inferInstanceAs (IsAffine (Spec _))`.

Establish `: IsAffineHom (h' ≫ W.ι ≫ p0 ≫ s)` using `isAffineHom_of_isAffine _`. Establish `: QuasiCompact (h' ≫ W.ι ≫ p0 ≫ s)` using `quasiCompact_iff_forall_isAffineOpen.mpr fun _ hU => (hU.preimage _).isCompact`. Establish `: QuasiCompact h'` using `QuasiCompact.of_comp h' (W.ι ≫ p0 ≫ s)`. Establish `: LocallyOfFiniteType (h' ≫ W.ι ≫ p0)`. Rewrite using `[← Category.assoc, hfac, hb, cbase]`.

Establish `: LocallyOfFiniteType (spMap (MvPolynomial.C : Γ(X, U.1) →+* CR m U))`. Rewrite using `[spMap, HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]`. Conclude with `RingHom.finiteType_algebraMap.2 inferInstance`. Establish `: IsOpenImmersion U.2.fromSpec` using `U.2.isOpenImmersion_fromSpec`. Use `infer_instance`.

Establish `: LocallyOfFiniteType h'` using `locallyOfFiniteType_of_comp h' (W.ι ≫ p0)`. Establish `hV : ValuativeCriterion h'`. Rewrite using `[ValuativeCriterion.iff]`. Use `⟨fun S => ?_, IsSeparated.valuativeCriterion h'⟩` and prove the remaining obligations. Take `⟨ψ, hψ⟩` from `sp_surj (A := CR m U) (B := S.K) S.i₁`.

Establish `hz : Set.range (S.i₂ ≫ W.ι) ⊆ W`. Rewrite using `[Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, ← Scheme.Opens.range_ι W]`. Conclude with `Set.image_subset_range _ _`. Establish `e : spMap ψ ≫ h = spMap (algebraMap S.R S.K) ≫ (S.i₂ ≫ W.ι)`. Rewrite using `[← hψ, ← hfac, ← Category.assoc, S.commSq.w, Category.assoc]`.

Take `⟨χ, hχ₁, hχ₂⟩` from `exists_lift hD hb hp hW hs _ hz ψ e`. Use `CommSq.HasLift.mk' ⟨spMap χ, ?_, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `spMap (algebraMap S.R S.K) ≫ spMap χ = S.i₁`. Rewrite using `[sp_comp, hχ₁, hψ]`. Rewrite using `[← cancel_mono W.ι, Category.assoc, hfac, hχ₂]`.

Establish `: IsProper h'` using `IsProper.of_valuativeCriterion h' hV`. Conclude with `(IsClosedImmersion.iff_isProper_and_mono h').2 ⟨inferInstance, inferInstance⟩`.
-/
theorem closed_of [Finite T] (hD : LeftInv D c) (hb : h ≫ p0 = cbase m U)
    (hp : ∀ en, ∃ hu, h ≫ p en = pt a (plk (uvec c w) en.2.1) hu) {W : P.Opens} (hW : IsCellOpen p0 p U D w W)
    {s : X ⟶ Sp O} [IsSeparated (p0 ≫ s)] (hs : ∀ en, p en ≫ PSpace.str _ _ = p0 ≫ s) :
    ∃ h' : Sp (CR m U) ⟶ W.toScheme, h' ≫ W.ι = h ∧ IsClosedImmersion h' := by
  have hr : Set.range h ⊆ Set.range W.ι := by
    rw [Scheme.Opens.range_ι]
    exact range_le hD hb hp hW
  let h' := IsOpenImmersion.lift W.ι h hr
  have hfac : h' ≫ W.ι = h := IsOpenImmersion.lift_fac _ _ _
  refine ⟨h', hfac, ?_⟩
  have : Mono h := mono_cell hD hb hp
  have : Mono h' := mono_of_mono_fac hfac
  have : IsAffine (Sp (CR m U)) := inferInstanceAs (IsAffine (Spec _))
  have : IsAffine (Sp O) := inferInstanceAs (IsAffine (Spec _))
  have : IsAffineHom (h' ≫ W.ι ≫ p0 ≫ s) := isAffineHom_of_isAffine _
  have : QuasiCompact (h' ≫ W.ι ≫ p0 ≫ s) :=
    quasiCompact_iff_forall_isAffineOpen.mpr fun _ hU => (hU.preimage _).isCompact
  have : QuasiCompact h' := QuasiCompact.of_comp h' (W.ι ≫ p0 ≫ s)
  have : LocallyOfFiniteType (h' ≫ W.ι ≫ p0) := by
    rw [← Category.assoc, hfac, hb, cbase]
    have : LocallyOfFiniteType (spMap (MvPolynomial.C : Γ(X, U.1) →+* CR m U)) := by
      rw [spMap, HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
      exact RingHom.finiteType_algebraMap.2 inferInstance
    have : IsOpenImmersion U.2.fromSpec := U.2.isOpenImmersion_fromSpec
    infer_instance
  have : LocallyOfFiniteType h' := locallyOfFiniteType_of_comp h' (W.ι ≫ p0)
  have hV : ValuativeCriterion h' := by
    rw [ValuativeCriterion.iff]
    refine ⟨fun S => ?_, IsSeparated.valuativeCriterion h'⟩
    obtain ⟨ψ, hψ⟩ := sp_surj (A := CR m U) (B := S.K) S.i₁
    have hz : Set.range (S.i₂ ≫ W.ι) ⊆ W := by
      rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, ← Scheme.Opens.range_ι W]
      exact Set.image_subset_range _ _
    have e : spMap ψ ≫ h = spMap (algebraMap S.R S.K) ≫ (S.i₂ ≫ W.ι) := by
      rw [← hψ, ← hfac, ← Category.assoc, S.commSq.w, Category.assoc]
    obtain ⟨χ, hχ₁, hχ₂⟩ := exists_lift hD hb hp hW hs _ hz ψ e
    refine CommSq.HasLift.mk' ⟨spMap χ, ?_, ?_⟩
    · change spMap (algebraMap S.R S.K) ≫ spMap χ = S.i₁
      rw [sp_comp, hχ₁, hψ]
    · rw [← cancel_mono W.ι, Category.assoc, hfac, hχ₂]
  have : IsProper h' := IsProper.of_valuativeCriterion h' hV
  exact (IsClosedImmersion.iff_isProper_and_mono h').2 ⟨inferInstance, inferInstance⟩

end

/- English proof (translation)
Introduce `O K _ _ β X s T _ m M B V α c D P p0 p h hcov hpl _ _ b w W hW`. Take `⟨N, i, hi, hi'⟩` from `hpl.proj`. Establish `: IsSeparated (PSpace.str O N)` using `inferInstance`. Establish `: IsSeparated (p0 ≫ s)`. Rewrite using `[← hi']`.

Use `infer_instance`. Conclude with `closed_of (hcov.inv b) (hpl.base b w) (hpl.plk b w) hW hpl.ovr`.
-/
theorem cell_closed : ∀ (O K : Type) [CommRing O] [Field K] (β : O →+* K) (X : Scheme.{0}) (s : X ⟶ Sp O) (T : Type) [Finite T] (m : T → ℕ) (M : ℕ) (B : Type) (V : B → X.affineOpens) (α : ∀ b, K →+* Γ(X, (V b).1)) (c D : ∀ b, Let m → Fin (M + 1) → Γ(X, (V b).1)) (P : Scheme.{0}) (p0 : P ⟶ X) (p : ∀ en : En m, P ⟶ PSpace O (plN M en.1)) (h : ∀ b, Pm m → (Sp (CR m (V b)) ⟶ P)), IsCover β s V α c D → IsPlk β s V α c p0 p h → IsNoetherianRing O → IsProjOver s → ∀ b w (W : P.Opens), IsCellOpen p0 p (V b) (D b) w W → ∃ h' : Sp (CR m (V b)) ⟶ W.toScheme, h' ≫ W.ι = h b w ∧ IsClosedImmersion h' := by
  intro O K _ _ β X s T _ m M B V α c D P p0 p h hcov hpl _ _ b w W hW
  obtain ⟨N, i, hi, hi'⟩ := hpl.proj
  have : IsSeparated (PSpace.str O N) := inferInstance
  have : IsSeparated (p0 ≫ s) := by
    rw [← hi']
    infer_instance
  exact closed_of (hcov.inv b) (hpl.base b w) (hpl.plk b w) hW hpl.ovr

end GlobalTheory.FlagEmb.CellClosed
