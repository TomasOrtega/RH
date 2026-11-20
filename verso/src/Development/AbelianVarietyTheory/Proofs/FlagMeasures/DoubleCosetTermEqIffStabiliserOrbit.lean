import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.VolPin
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Vanish
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AtBase
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PlacesOf
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalUnipotentGroupsLatticesGlobalCoordinatesStatement
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HL.TermOrbit

section Places

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E}

/- English proof (translation)
Establish `hb : ∀ i : Fin n, A.bc p (Pi.single i 1) = Pi.single i 1`. Introduce `i`. Use function extensionality and compare the values at `j`. Simplify using `only [Places.bc, Pi.single_apply]`. Apply the tactic sequence `split_ifs <;> simp`.

Apply `LinearEquiv.toLinearMap_injective` to reduce the goal to its premises. Apply `(Pi.basisFun (A.loc p).Ep (Fin n)).ext` to reduce the goal to its premises. Introduce `i`. Simplify using `only [Pi.basisFun_apply, LinearEquiv.coe_coe]`. Rewrite using `[← hb i, h₁, h₂]`.
-/
theorem ext_eq (A : Places F E sig) {n : ℕ} (p : IsDedekindDomain.HeightOneSpectrum (𝓞 F))
    {g : (Fin n → E) ≃ₗ[E] (Fin n → E)} {g₁ g₂ : (Fin n → (A.loc p).Ep) ≃ₗ[(A.loc p).Ep] (Fin n → (A.loc p).Ep)}
    (h₁ : A.Ext p g g₁) (h₂ : A.Ext p g g₂) : g₁ = g₂ := by
  have hb : ∀ i : Fin n, A.bc p (Pi.single i 1) = Pi.single i 1 := by
    intro i; funext j
    simp only [Places.bc, Pi.single_apply]
    split_ifs <;> simp
  apply LinearEquiv.toLinearMap_injective
  apply (Pi.basisFun (A.loc p).Ep (Fin n)).ext
  intro i
  simp only [Pi.basisFun_apply, LinearEquiv.coe_coe]
  rw [← hb i, h₁, h₂]

/- English proof (translation)
Introduce `p`. Take `⟨g₁, hg₁, e₁⟩` from `h p`. Take `⟨g₂, hg₂, e₂⟩` from `h' p`. Take `rfl` from `ext_eq A p e₁ e₂`. Conclude with `⟨g₁, ⟨hg₁, hg₂⟩, e₁⟩`.
-/
theorem mem_rat_inf (A : Places F E sig) {n : ℕ}
    (K K' : ∀ p, Subgroup ((Fin n → (A.loc p).Ep) ≃ₗ[(A.loc p).Ep] (Fin n → (A.loc p).Ep)))
    {g : (Fin n → E) ≃ₗ[E] (Fin n → E)} (h : g ∈ A.rat K) (h' : g ∈ A.rat K') :
    g ∈ A.rat (fun p => K p ⊓ K' p) := by
  intro p
  obtain ⟨g₁, hg₁, e₁⟩ := h p
  obtain ⟨g₂, hg₂, e₂⟩ := h' p
  obtain rfl := ext_eq A p e₁ e₂
  exact ⟨g₁, ⟨hg₁, hg₂⟩, e₁⟩

/- English proof (translation)
Introduce `p`. Take `⟨g₁, hg₁, e₁⟩` from `h p`. Conclude with `⟨g₁, hK p hg₁, e₁⟩`.
-/
theorem rat_mono (A : Places F E sig) {n : ℕ}
    {K K' : ∀ p, Subgroup ((Fin n → (A.loc p).Ep) ≃ₗ[(A.loc p).Ep] (Fin n → (A.loc p).Ep))}
    (hK : ∀ p, K p ≤ K' p) {g : (Fin n → E) ≃ₗ[E] (Fin n → E)} (h : g ∈ A.rat K) : g ∈ A.rat K' := by
  intro p
  obtain ⟨g₁, hg₁, e₁⟩ := h p
  exact ⟨g₁, hK p hg₁, e₁⟩

end Places

end GlobalTheory.HL.TermOrbit

namespace GlobalTheory.HL.TermOrbit

section Coord

variable {D : D7} {Z : LocDat D} {T T' : D.host.E} {F0 : LFlag (VS D) D.R.rS T} {F0' : LFlag (VS D) D.R.rS T'}
  {FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS} {G : GFrames (placesOf Z) D.R.rS D.R.k}
  (c : GCoord Z F0 F0' FP G)

/- English proof (translation)
Use extensionality with `x`. Simplify using `[GCoord.grp, LinearEquiv.mul_apply]`.
-/
theorem grp_mul (ρ a b : (VS D).V ≃ₗ[D.host.E] (VS D).V) : c.grp ρ (a * b) = c.grp ρ a * c.grp ρ b := by
  ext x; simp [GCoord.grp, LinearEquiv.mul_apply]

/- English proof (translation)
Use extensionality with `x`. Simplify using `[GCoord.grp]`.
-/
theorem grp_one (ρ : (VS D).V ≃ₗ[D.host.E] (VS D).V) : c.grp ρ 1 = 1 := by
  ext x; simp [GCoord.grp]

/- English proof (translation)
Use `eq_inv_of_mul_eq_one_left ?_` and prove the remaining obligations. Rewrite using `[← grp_mul, inv_mul_cancel, grp_one]`.
-/
theorem grp_inv (ρ a : (VS D).V ≃ₗ[D.host.E] (VS D).V) : c.grp ρ a⁻¹ = (c.grp ρ a)⁻¹ := by
  refine eq_inv_of_mul_eq_one_left ?_
  rw [← grp_mul, inv_mul_cancel, grp_one]

/- English proof (translation)
Use extensionality with `x`. Simplify using `[GCoord.grp, LinearEquiv.mul_eq_trans, LinearEquiv.symm_trans_apply]`.
-/
theorem grp_conj (ρ τ a : (VS D).V ≃ₗ[D.host.E] (VS D).V) : c.grp (ρ * τ) a = c.grp ρ (τ * a * τ⁻¹) := by
  ext x; simp [GCoord.grp, LinearEquiv.mul_eq_trans, LinearEquiv.symm_trans_apply]

/- English proof (translation)
Use extensionality with `x`. Simplify using `[GCoord.grp]`.
-/
theorem grp_surj (ρ : (VS D).V ≃ₗ[D.host.E] (VS D).V) (s : G.GLV) :
    c.grp ρ (((ρ.trans c.e).trans s).trans (ρ.trans c.e).symm) = s := by
  ext x; simp [GCoord.grp]

/- English proof (translation)
Simplify using `only [GCoord.lat]`. Rewrite using `[← Submodule.map_comp]`. Use `congr 1`. Use extensionality with `x`. Simplify using `[GCoord.grp, LinearEquiv.mul_apply]`.
-/
theorem lat_map_grp (ρ a σ : (VS D).V ≃ₗ[D.host.E] (VS D).V) (Λ : Submodule (𝓞 D.host.E) (VS D).V) :
    (c.lat (ρ * a) Λ).map (((c.grp ρ σ : G.GLV) : G.V →ₗ[D.host.E] G.V).restrictScalars (𝓞 D.host.E)) =
      c.lat (ρ * (σ * a)) Λ := by
  simp only [GCoord.lat]
  rw [← Submodule.map_comp]
  congr 1
  ext x; simp [GCoord.grp, LinearEquiv.mul_apply]

/- English proof (translation)
Simplify using `only [GCoord.lat, Formalism.HermitianLatticesTheory.gmap]`. Rewrite using `[← Submodule.map_comp]`. Use `congr 1`.
-/
theorem lat_mul (ρ a : (VS D).V ≃ₗ[D.host.E] (VS D).V) (Λ : Submodule (𝓞 D.host.E) (VS D).V) :
    c.lat (ρ * a) Λ = c.lat ρ (Formalism.HermitianLatticesTheory.gmap a Λ) := by
  simp only [GCoord.lat, Formalism.HermitianLatticesTheory.gmap]
  rw [← Submodule.map_comp]
  congr 1

/- English proof (translation)
The claim follows from `Submodule.map_injective_of_injective (f := (((ρ.trans c.e : (VS D).V ≃ₗ[D.host.E] G.V) : (VS D).V →ₗ[D.host.E] G.V).restrictScalars (𝓞 D.host.E))) (fun x y hxy => (ρ.trans c.e).injective hxy) h`.
-/
theorem lat_inj (ρ : (VS D).V ≃ₗ[D.host.E] (VS D).V) {Λ₁ Λ₂ : Submodule (𝓞 D.host.E) (VS D).V}
    (h : c.lat ρ Λ₁ = c.lat ρ Λ₂) : Λ₁ = Λ₂ :=
  Submodule.map_injective_of_injective
    (f := (((ρ.trans c.e : (VS D).V ≃ₗ[D.host.E] G.V) : (VS D).V →ₗ[D.host.E] G.V).restrictScalars (𝓞 D.host.E)))
    (fun x y hxy => (ρ.trans c.e).injective hxy) h

end Coord

/- English proof (translation)
Simplify using `only [Formalism.HermitianLatticesTheory.gmap]`. Rewrite using `[← Submodule.map_comp]`. Both sides reduce to the same expression.
-/
theorem gmap_mul {D : D7} (a b : (VS D).V ≃ₗ[D.host.E] (VS D).V) (Λ : Submodule (𝓞 D.host.E) (VS D).V) :
    Formalism.HermitianLatticesTheory.gmap (a * b) Λ = Formalism.HermitianLatticesTheory.gmap a (Formalism.HermitianLatticesTheory.gmap b Λ) := by
  simp only [Formalism.HermitianLatticesTheory.gmap]
  rw [← Submodule.map_comp]
  rfl

/- English proof (translation)
Simplify using `only [Formalism.HermitianLatticesTheory.gmap]`. Conclude with `Submodule.map_id Λ`.
-/
theorem gmap_one {D : D7} (Λ : Submodule (𝓞 D.host.E) (VS D).V) : Formalism.HermitianLatticesTheory.gmap (1 : (VS D).V ≃ₗ[D.host.E] (VS D).V) Λ = Λ := by
  simp only [Formalism.HermitianLatticesTheory.gmap]
  exact Submodule.map_id Λ

end GlobalTheory.HL.TermOrbit

namespace GlobalTheory.HL.TermOrbit

/- English proof (translation)
Take `⟨l, hl, l', hl', cl⟩` from `t`. Take `⟨k, hk, k', hk', ck⟩` from `t'`. Simplify using `only at h₁ h₂`. Substitute `h₁ h₂` using the available equality. Take `⟨a, ha, b, hb, e⟩` from `h`.

Establish `hc : cl = ck`. Rewrite using `[← Quot.out_eq cl, ← Quot.out_eq ck]`. Conclude with `Quot.sound ⟨a, ha, b, hb, e⟩`. Substitute `hc` using the available equality. Both sides reduce to the same expression.
-/
theorem gterm_eq_of_rel {D : D7} {X : HidaSetting D} {u u' : D.what₂.Word}
    {F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)} {F0' : FlagG (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)}
    {what₂ rows' : Finset (Submodule (𝓞 D.host.E) (VS D).V)} {t t' : GTerm X u u' F0 F0' what₂ rows'}
    (h₁ : t.lam = t'.lam) (h₂ : t.lam' = t'.lam')
    (h : ∃ a ∈ NLam t.lam (lf D F0), ∃ b ∈ NLam t.lam' (lf D F0'), t'.lin = a * t.lin * b) : t = t' := by
  obtain ⟨l, hl, l', hl', cl⟩ := t
  obtain ⟨k, hk, k', hk', ck⟩ := t'
  simp only at h₁ h₂
  subst h₁ h₂
  obtain ⟨a, ha, b, hb, e⟩ := h
  have hc : cl = ck := by
    rw [← Quot.out_eq cl, ← Quot.out_eq ck]
    exact Quot.sound ⟨a, ha, b, hb, e⟩
  subst hc
  rfl

/- English proof (translation)
Introduce `D X Y u u' hst hk w F00 F'0 FP hZ hG hAt G c t₀ ρ U U' hmv t t' n m n' m' e₁ e₂ e₃ e₄ hnm hnm'`. Take `⟨hn, hm, ht⟩` from `hnm`. Take `⟨hn', hm', ht'⟩` from `hnm'`. Establish `hI` using `GlobalTheory.T.rational_unipotent_groups_lattices_global_coordinates D X Y u u' hst hk w F00 F'0 FP hZ hG hAt G c t₀ ρ U U' hmv`. Establish `hN` using `hI.1`.

Establish `hN'` using `hI.2.1`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `rfl`. Establish `key : n' * n⁻¹ = t₀.lin * (m' * m⁻¹) * t₀.lin⁻¹`. Combine the equalities or inequalities in the displayed calculation.

Use `⟨c.grp ρ (n' * n⁻¹), ?_, ?_⟩` and prove the remaining obligations. Establish `h1 : c.grp ρ (n' * n⁻¹) ∈ G.N`. Rewrite using `[grp_mul, grp_inv]`. Conclude with `G.N.mul_mem ((hN n').1 hn') (G.N.inv_mem ((hN n).1 hn))`. Establish `h2 : c.grp ρ (n' * n⁻¹) ∈ G.N'`.

Rewrite using `[key, ← grp_conj, grp_mul, grp_inv]`. Conclude with `G.N'.mul_mem ((hN' m').1 hm') (G.N'.inv_mem ((hN' m).1 hm))`. Conclude with `mem_rat_inf _ _ _ h1 h2`. Rewrite using `[lat_map_grp]`. Use `congr 2`.

Use `group`. Introduce and unpack `⟨s, hs, hmap⟩ set σ := ((ρ.trans c.e).trans s).trans (ρ.trans c.e).symm with hσdef`. Establish `hsσ : c.grp ρ σ = s` using `grp_surj c ρ s`. Establish `hsN : s ∈ G.N` using `rat_mono _ (fun p => inf_le_left) hs`. Establish `hsN' : s ∈ G.N'` using `rat_mono _ (fun p => inf_le_right) hs`.

Establish `hΛ : Formalism.HermitianLatticesTheory.gmap (σ * n) t.lam = Formalism.HermitianLatticesTheory.gmap n' t.lam`. Rewrite `hmap` using `[← hsσ, lat_map_grp, e₃, ← e₁, lat_mul, lat_mul]`. Conclude with `lat_inj c ρ hmap`. Use `set a := n'⁻¹ * σ * n with ha_def`. Use `set b := m⁻¹ * t₀.lin⁻¹ * σ⁻¹ * t₀.lin * m' with hb_def`.

Establish `haN : a ∈ NRat (lf D (X.Fu u))`. Rewrite using `[hN, ha_def, grp_mul, grp_mul, grp_inv, hsσ]`. Conclude with `G.N.mul_mem (G.N.mul_mem (G.N.inv_mem ((hN n').1 hn')) hsN) ((hN n).1 hn)`. Establish `hσ' : c.grp (ρ * t₀.lin) (t₀.lin⁻¹ * σ * t₀.lin) = s`. Rewrite using `[grp_conj, ← hsσ]`.

Use `congr 1`. Use `group`. Establish `hbN : b ∈ NRat (lf D (X.Fu u'))`. Establish `eb : b = m⁻¹ * (t₀.lin⁻¹ * σ * t₀.lin)⁻¹ * m'` using `by rw [hb_def]; group`. Rewrite using `[hN', eb, grp_mul, grp_mul, grp_inv, grp_inv, hσ']`.

Conclude with `G.N'.mul_mem (G.N'.mul_mem (G.N'.inv_mem ((hN' m).1 hm)) (G.N'.inv_mem hsN')) ((hN' m').1 hm')`. Establish `haΛ : Formalism.HermitianLatticesTheory.gmap a t.lam = t.lam`. Rewrite using `[ha_def, mul_assoc, gmap_mul, hΛ, ← gmap_mul, inv_mul_cancel, gmap_one]`. Establish `haΛ' : Formalism.HermitianLatticesTheory.gmap a⁻¹ t.lam = t.lam` using `by conv_lhs => rw [← haΛ]`. Rewrite using `[← gmap_mul, inv_mul_cancel, gmap_one]`.

Establish `hl : Formalism.HermitianLatticesTheory.gmap t.lin t.lam' = t.lam` using `t.rep.2.2.2.1`. Establish `hl' : Formalism.HermitianLatticesTheory.gmap t'.lin t'.lam' = t'.lam` using `t'.rep.2.2.2.1`. Establish `eb2 : b = t.lin⁻¹ * a⁻¹ * t'.lin`. Rewrite using `[hb_def, ha_def, ht, ht']`. Use `group`.

Establish `hbΛ : Formalism.HermitianLatticesTheory.gmap b t.lam' = t.lam'`. Establish `hl'' : Formalism.HermitianLatticesTheory.gmap t'.lin t.lam' = t.lam` using `by rw [e₂, ← e₄, hl', e₃, e₁]`. Rewrite using `[eb2, gmap_mul, gmap_mul, hl'', haΛ', ← hl, ← gmap_mul, inv_mul_cancel, gmap_one]`. Use `gterm_eq_of_rel (by rw [e₁, e₃]) (by rw [e₂, e₄]) ⟨a, ⟨⟨haN.1, haΛ⟩, haN.2⟩, b, ⟨⟨hbN.1, hbΛ⟩, hbN.2⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[ht, ht', ha_def, hb_def]`.

Use `group`.
-/
theorem term_eq_iff_lRel : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), Formalism.MainNotions.S.Cnt.Stand D u u' → 4 * D.R.rS + 7 ≤ D.R.k → ∀ (w : Point D.host.E (D.R.rS + 1)) (F00 : LFlag (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (F'0 : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (FP : ∀ p : PlF D, LocNG.FPair (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p) D.R.rS), ZhatOM (ZhatL F00 F'0) = ptMat w → Gval F00 F'0 ≠ 0 → (∀ p, AtBase (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p F00 F'0 (Tu D u) (Tu D u') (FP p) ∧ (FP p).RelG (LocNG.theta (Y.M p))) → ∀ (G : GFrames (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)) D.R.rS D.R.k) (c : GCoord (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) F00 F'0 FP G), ∀ (t₀ : TauC Y u u') (ρ : ((VS D).V ≃ₗ[D.host.E] (VS D).V)) (U U' : Formalism.L2.SG.PairVal.MatR D), MovesTo F00 F'0 (lf D (X.Fu u)) t₀.frame ρ U U' → ∀ (t t' : TauC Y u u') n m n' m', t.lam = t₀.lam → t.lam' = t₀.lam' → t'.lam = t₀.lam → t'.lam' = t₀.lam' → n ∈ NRat (lf D (X.Fu u)) ∧ m ∈ NRat (lf D (X.Fu u')) ∧ t.lin = n⁻¹ * t₀.lin * m → n' ∈ NRat (lf D (X.Fu u)) ∧ m' ∈ NRat (lf D (X.Fu u')) ∧ t'.lin = n'⁻¹ * t₀.lin * m' → (t = t' ↔ G.LRel (c.lat (ρ * n) t.lam) (c.lat (ρ * n') t'.lam)) := by
  intro D X Y u u' hst hk w F00 F'0 FP hZ hG hAt G c t₀ ρ U U' hmv t t' n m n' m' e₁ e₂ e₃ e₄ hnm hnm'
  obtain ⟨hn, hm, ht⟩ := hnm
  obtain ⟨hn', hm', ht'⟩ := hnm'
  have hI := GlobalTheory.T.rational_unipotent_groups_lattices_global_coordinates D X Y u u' hst hk w F00 F'0 FP hZ hG hAt G c t₀ ρ U U' hmv
  have hN := hI.1
  have hN' := hI.2.1
  constructor
  · rintro rfl
    have key : n' * n⁻¹ = t₀.lin * (m' * m⁻¹) * t₀.lin⁻¹ := by
      calc n' * n⁻¹ = n' * (n⁻¹ * t₀.lin * m) * m⁻¹ * t₀.lin⁻¹ := by group
        _ = n' * (n'⁻¹ * t₀.lin * m') * m⁻¹ * t₀.lin⁻¹ := by rw [← ht, ← ht']
        _ = t₀.lin * (m' * m⁻¹) * t₀.lin⁻¹ := by group
    refine ⟨c.grp ρ (n' * n⁻¹), ?_, ?_⟩
    · have h1 : c.grp ρ (n' * n⁻¹) ∈ G.N := by
        rw [grp_mul, grp_inv]
        exact G.N.mul_mem ((hN n').1 hn') (G.N.inv_mem ((hN n).1 hn))
      have h2 : c.grp ρ (n' * n⁻¹) ∈ G.N' := by
        rw [key, ← grp_conj, grp_mul, grp_inv]
        exact G.N'.mul_mem ((hN' m').1 hm') (G.N'.inv_mem ((hN' m).1 hm))
      exact mem_rat_inf _ _ _ h1 h2
    · rw [lat_map_grp]
      congr 2
      group
  · rintro ⟨s, hs, hmap⟩
    set σ := ((ρ.trans c.e).trans s).trans (ρ.trans c.e).symm with hσdef
    have hsσ : c.grp ρ σ = s := grp_surj c ρ s
    have hsN : s ∈ G.N := rat_mono _ (fun p => inf_le_left) hs
    have hsN' : s ∈ G.N' := rat_mono _ (fun p => inf_le_right) hs
    have hΛ : Formalism.HermitianLatticesTheory.gmap (σ * n) t.lam = Formalism.HermitianLatticesTheory.gmap n' t.lam := by
      rw [← hsσ, lat_map_grp, e₃, ← e₁, lat_mul, lat_mul] at hmap
      exact lat_inj c ρ hmap
    set a := n'⁻¹ * σ * n with ha_def
    set b := m⁻¹ * t₀.lin⁻¹ * σ⁻¹ * t₀.lin * m' with hb_def
    have haN : a ∈ NRat (lf D (X.Fu u)) := by
      rw [hN, ha_def, grp_mul, grp_mul, grp_inv, hsσ]
      exact G.N.mul_mem (G.N.mul_mem (G.N.inv_mem ((hN n').1 hn')) hsN) ((hN n).1 hn)
    have hσ' : c.grp (ρ * t₀.lin) (t₀.lin⁻¹ * σ * t₀.lin) = s := by
      rw [grp_conj, ← hsσ]
      congr 1
      group
    have hbN : b ∈ NRat (lf D (X.Fu u')) := by
      have eb : b = m⁻¹ * (t₀.lin⁻¹ * σ * t₀.lin)⁻¹ * m' := by rw [hb_def]; group
      rw [hN', eb, grp_mul, grp_mul, grp_inv, grp_inv, hσ']
      exact G.N'.mul_mem (G.N'.mul_mem (G.N'.inv_mem ((hN' m).1 hm)) (G.N'.inv_mem hsN')) ((hN' m').1 hm')
    have haΛ : Formalism.HermitianLatticesTheory.gmap a t.lam = t.lam := by
      rw [ha_def, mul_assoc, gmap_mul, hΛ, ← gmap_mul, inv_mul_cancel, gmap_one]
    have haΛ' : Formalism.HermitianLatticesTheory.gmap a⁻¹ t.lam = t.lam := by
      conv_lhs => rw [← haΛ]
      rw [← gmap_mul, inv_mul_cancel, gmap_one]
    have hl : Formalism.HermitianLatticesTheory.gmap t.lin t.lam' = t.lam := t.rep.2.2.2.1
    have hl' : Formalism.HermitianLatticesTheory.gmap t'.lin t'.lam' = t'.lam := t'.rep.2.2.2.1
    have eb2 : b = t.lin⁻¹ * a⁻¹ * t'.lin := by
      rw [hb_def, ha_def, ht, ht']; group
    have hbΛ : Formalism.HermitianLatticesTheory.gmap b t.lam' = t.lam' := by
      have hl'' : Formalism.HermitianLatticesTheory.gmap t'.lin t.lam' = t.lam := by rw [e₂, ← e₄, hl', e₃, e₁]
      rw [eb2, gmap_mul, gmap_mul, hl'', haΛ', ← hl, ← gmap_mul, inv_mul_cancel, gmap_one]
    refine gterm_eq_of_rel (by rw [e₁, e₃]) (by rw [e₂, e₄]) ⟨a, ⟨⟨haN.1, haΛ⟩, haN.2⟩, b, ⟨⟨hbN.1, hbΛ⟩, hbN.2⟩, ?_⟩
    rw [ht, ht', ha_def, hb_def]
    group

end GlobalTheory.HL.TermOrbit
