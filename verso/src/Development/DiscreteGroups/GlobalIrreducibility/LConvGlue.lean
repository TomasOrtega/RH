import Mathlib
import Development.DiscreteGroups.GlobalIrreducibility.LConvCut
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RankinSelbergTestFunction
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AlgebraMapIntertwiningMapBijectiveOfIsSmooth
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SchwartzBilinear.BlockTriangularLevi

set_option linter.unusedSectionVars false

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel GlobalTheory.LocLanglands GlobalTheory.Whittaker Matrix

namespace DiscreteGroups.sglob.LConv

section Theta

variable {k : Type} [Field k]

/- English proof (translation)
The claim follows from `Units.ext (antidiag_mul_self n k)`.
-/
theorem longElt_mul_self (n : ℕ) : longElt n k * longElt n k = 1 := Units.ext (antidiag_mul_self n k)

variable (k) in

def theta (n : ℕ) : GL (Fin n) k →* GL (Fin n) k :=
  (MulAut.conj (longElt n k)).toMonoidHom.comp (GlobalTheory.CuspRep.invT n k)

/- English proof (translation)
Simplify using `[theta, MulAut.conj_apply, inv_eq_of_mul_eq_one_right (longElt_mul_self (k := k) n)]`.
-/
theorem theta_apply {n : ℕ} (g : GL (Fin n) k) :
    theta k n g = longElt n k * GlobalTheory.CuspRep.invT n k g * longElt n k := by
  simp [theta, MulAut.conj_apply, inv_eq_of_mul_eq_one_right (longElt_mul_self (k := k) n)]

/- English proof (translation)
Rewrite using `[theta_apply, theta_apply, GlobalTheory.T.long_element_conj_involutive]`.
-/
theorem theta_theta {n : ℕ} (g : GL (Fin n) k) : theta k n (theta k n g) = g := by
  rw [theta_apply, theta_apply, GlobalTheory.T.long_element_conj_involutive]

/- English proof (translation)
Rewrite using `[theta_apply, mul_assoc, longElt_mul_self, mul_one]`. Both sides reduce to the same expression.
-/
theorem tilde_eq {n : ℕ} (g : GL (Fin n) k) : tilde g = theta k n g * longElt n k := by
  rw [theta_apply, mul_assoc, longElt_mul_self, mul_one]
  rfl

/- English proof (translation)
Simplify using `only [corner]`. Rewrite using `[← map_mul, Prod.mk_mul_mk, mul_one]`.
-/
theorem corner_mul {m : ℕ} (g h : GL (Fin m) k) : corner (g * h) = corner g * corner h := by
  simp only [corner]
  rw [← map_mul, Prod.mk_mul_mk, mul_one]

/- English proof (translation)
The claim follows from `map_one (emb₂ k (stdSum (rfl : m + 1 = m + 1)))`.
-/
theorem corner_one {m : ℕ} : corner (1 : GL (Fin m) k) = 1 := map_one (emb₂ k (stdSum (rfl : m + 1 = m + 1)))

variable {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]

/- English proof (translation)
Introduce `u hu x`. Take `⟨h1, h2⟩` from `GlobalTheory.T.long_element_conj_unipotent_borel k n u hu`. Use `show l (ρ (theta k n u) x) = _`. Rewrite using `[theta_apply, hl _ h1, h2, AddChar.inv_apply]`.
-/
theorem isFunctional_theta {ψ : AddChar k Circle} {ρ : Representation ℂ (GL (Fin n) k) V} {l : Module.Dual ℂ V}
    (hl : IsFunctional ψ ρ l) : IsFunctional ψ⁻¹ (ρ.comp (theta k n)) l := by
  intro u hu x
  obtain ⟨h1, h2⟩ := GlobalTheory.T.long_element_conj_unipotent_borel k n u hu
  show l (ρ (theta k n u) x) = _
  rw [theta_apply, hl _ h1, h2, AddChar.inv_apply]

/- English proof (translation)
Set `e : Subrepresentation (ρ.comp f : Representation ℂ G' V) ≃o Subrepresentation ρ` to `{ toFun := fun W => ⟨W.toSubmodule, fun g v hv => by`. Take `⟨g', rfl⟩` from `hf g`. Conclude with `W.apply_mem_toSubmodule g' hv⟩`. Use `invFun := fun W => ⟨W.toSubmodule, fun g v hv => W.apply_mem_toSubmodule (f g) hv⟩`. Use `left_inv := fun _ => rfl`.

Use `right_inv := fun _ => rfl`. Use the proof step `map_rel_iff' := Iff.rfl }`. Conclude with `e.isSimpleOrder_iff.2 hρ`.
-/
theorem isIrreducible_comp_surjective {G G' : Type} [Group G] [Group G'] {ρ : Representation ℂ G V}
    (hρ : ρ.IsIrreducible) (f : G' →* G) (hf : Function.Surjective f) :
    Representation.IsIrreducible (ρ.comp f : Representation ℂ G' V) := by
  let e : Subrepresentation (ρ.comp f : Representation ℂ G' V) ≃o Subrepresentation ρ :=
    { toFun := fun W => ⟨W.toSubmodule, fun g v hv => by
        obtain ⟨g', rfl⟩ := hf g
        exact W.apply_mem_toSubmodule g' hv⟩
      invFun := fun W => ⟨W.toSubmodule, fun g v hv => W.apply_mem_toSubmodule (f g) hv⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_rel_iff' := Iff.rfl }
  exact e.isSimpleOrder_iff.2 hρ

end Theta

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/- English proof (translation)
Establish `hinvc : Continuous (GlobalTheory.CuspRep.invT n k)` using `Units.continuous_iff.2 ⟨Units.continuous_coe_inv.matrix_transpose, Units.continuous_val.matrix_transpose⟩`. Establish `: (theta k n : GL (Fin n) k → GL (Fin n) k) = fun g => longElt n k * GlobalTheory.CuspRep.invT n k g * longElt n k` using `funext theta_apply`. Rewrite using `[this]`. Conclude with `(continuous_const.mul hinvc).mul continuous_const`.
-/
theorem continuous_theta (n : ℕ) : Continuous (theta k n) := by
  have hinvc : Continuous (GlobalTheory.CuspRep.invT n k) :=
    Units.continuous_iff.2 ⟨Units.continuous_coe_inv.matrix_transpose, Units.continuous_val.matrix_transpose⟩
  have : (theta k n : GL (Fin n) k → GL (Fin n) k) =
      fun g => longElt n k * GlobalTheory.CuspRep.invT n k g * longElt n k := funext theta_apply
  rw [this]
  exact (continuous_const.mul hinvc).mul continuous_const

/- English proof (translation)
The claim follows from `(continuous_leviEmb k _).comp ((continuous_leviTwo k).comp (continuous_id.prodMk continuous_const))`.
-/
theorem continuous_corner (m : ℕ) : Continuous (corner : GL (Fin m) k → GL (Fin (m + 1)) k) :=
  (continuous_leviEmb k _).comp ((continuous_leviTwo k).comp (continuous_id.prodMk continuous_const))

def thetaIrr {n : ℕ} (σ : IrrRep (GL (Fin n) k)) : IrrRep (GL (Fin n) k) :=
  ⟨σ.V, σ.ρ.comp (theta k n), fun x => (σ.smooth x).preimage (continuous_theta n),
    isIrreducible_comp_surjective σ.irr _ fun g => ⟨_, theta_theta g⟩⟩

/- English proof (translation)
Use `(IsLocallyConstant.iff_exists_open _).2 fun g => ⟨(fun x => g⁻¹ * x) ⁻¹' {x | ρ x v = v}, (hs v).preimage (continuous_const.mul continuous_id), by simp, fun x hx => ?_⟩` and prove the remaining obligations. Establish `h : ρ (g⁻¹ * x) v = v` using `hx`. Use `conv_rhs => rw [← h]`. Rewrite using `[← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left]`.
-/
theorem isLocallyConstant_orbit {G V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V} (hs : IsSmooth ρ) (v : V) :
    IsLocallyConstant fun g => ρ g v := by
  refine (IsLocallyConstant.iff_exists_open _).2 fun g => ⟨(fun x => g⁻¹ * x) ⁻¹' {x | ρ x v = v},
    (hs v).preimage (continuous_const.mul continuous_id), by simp, fun x hx => ?_⟩
  have h : ρ (g⁻¹ * x) v = v := hx
  conv_rhs => rw [← h]
  rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left]

/- English proof (translation)
Establish `: (⇑(ψ⁻¹ : AddChar k Circle)) = fun x => ψ (-x)` using `funext (AddChar.inv_apply ψ)`. Rewrite using `[this]`. Conclude with `h.comp continuous_neg`.
-/
theorem continuous_inv_addChar {ψ : AddChar k Circle} (h : Continuous ψ) :
    Continuous (ψ⁻¹ : AddChar k Circle) := by
  have : (⇑(ψ⁻¹ : AddChar k Circle)) = fun x => ψ (-x) := funext (AddChar.inv_apply ψ)
  rw [this]
  exact h.comp continuous_neg

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] in
/- English proof (translation)
The claim follows from `_root_.UpperTheory.Reformulated.B.P6.BlockTriangularLevi.DiscreteGroups.sglob.LConv.IsWhitTest.sub h h'`.
-/
theorem IsWhitTest.sub {m : ℕ} {ψ : AddChar k Circle} {f f' : GL (Fin m) k → ℂ} (h : IsWhitTest ψ f)
    (h' : IsWhitTest ψ f') : IsWhitTest ψ fun g => f g - f' g :=
  _root_.UpperTheory.Reformulated.B.P6.BlockTriangularLevi.DiscreteGroups.sglob.LConv.IsWhitTest.sub h h'

/- English proof (translation)
Establish `hs2 : IsSmooth (π.ρ.comp (theta k (m + 1)))` using `(thetaIrr π).smooth`. Establish `hl2` using `isFunctional_theta hl`. Establish `hJ : ∀ (a b : ℕ) (h : ∑ i, ![a, b] i = m + 1), 0 < a → 0 < b → ∀ x : π.V, x ∈ twKer π.ρ (unipRad k (stdBlocks ![a, b] h)) 1`. Introduce `a b h ha hb x`. Use `Submodule.Quotient.subsingleton_iff.1 (hcusp.2 2 ![a, b] (stdBlocks ![a, b] h) (GlobalTheory.T.unipRad_stdBlocks_two_ne_bot' k (m + 1) a b h ha hb))` as an intermediate fact.

Rewrite using `[this]`. Conclude with `Submodule.mem_top`. Establish `hJ2 : ∀ (a b : ℕ) (h : ∑ i, ![a, b] i = m + 1), 0 < a → 0 < b → ∀ x : π.V, x ∈ twKer (π.ρ.comp (theta k (m + 1))) (unipRad k (stdBlocks ![a, b] h)) 1`. Introduce `a b h ha hb x`. Establish `h' : ∑ i, ![b, a] i = m + 1`.

Simplify using `only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at h ⊢`. Use linear arithmetic over natural numbers and integers. Use `(Submodule.span_le.2 ?_) (hJ b a h' hb ha x)` and prove the remaining obligations. Introduce and unpack `_ ⟨n, y, rfl⟩`. Use `Submodule.subset_span ⟨⟨theta k (m + 1) n, ?_⟩, y, ?_⟩` and prove the remaining obligations.

Rewrite using `[theta_apply]`. Conclude with `GlobalTheory.T.long_element_conj_unipotent_radical k (m + 1) b a h' h n n.2`. Simplify using `only [MonoidHom.one_apply, Units.val_one, one_smul, MonoidHom.comp_apply]`. Rewrite using `[theta_theta]`. Establish `hψ'1 : (ψ⁻¹ : AddChar k Circle) ≠ 1` using `fun h => hψ1 (inv_eq_one.1 h)`.

Take `⟨C2, hC2, hsupp2⟩` from `exists_compact_mod_unipB_whittaker k ψ⁻¹ (continuous_inv_addChar hψc) hψ'1 m π.V (π.ρ.comp (theta k (m + 1))) hs2 hJ2 l hl2 (π.ρ (longElt (m + 1) k) v)`. Establish `key : (fun g : GL (Fin m) k => l (π.ρ (tilde (corner g)) v)) = fun g => l ((π.ρ.comp (theta k (m + 1))) (corner g) (π.ρ (longElt (m + 1) k) v))`. Use function extensionality and compare the values at `g`. Rewrite using `[tilde_eq, map_mul, Module.End.mul_apply]`. Both sides reduce to the same expression.

Rewrite using `[key]`. Use `⟨fun u hu g => ?_, ?_, C2, hC2, hsupp2⟩` and prove the remaining obligations. Take `⟨h1, h2⟩` from `GlobalTheory.T.glCornerEmbedding_upperUnitriangular_superDiagonalSum k m u hu beta_reduce`. Rewrite using `[corner_mul, map_mul, Module.End.mul_apply, hl2 _ h1, h2]`. Conclude with `((isLocallyConstant_orbit hs2 _).comp_continuous (continuous_corner m)).comp l`.
-/
theorem isWhitTest_tilde {ψ : AddChar k Circle} (hψc : Continuous ψ) (hψ1 : ψ ≠ 1) {m : ℕ}
    (π : IrrRep (GL (Fin (m + 1)) k)) (hcusp : IsCuspidal π.ρ) {l : Module.Dual ℂ π.V} (hl : IsFunctional ψ π.ρ l)
    (v : π.V) : IsWhitTest ψ⁻¹ fun g : GL (Fin m) k => l (π.ρ (tilde (corner g)) v) := by
  have hs2 : IsSmooth (π.ρ.comp (theta k (m + 1))) := (thetaIrr π).smooth
  have hl2 := isFunctional_theta hl
  have hJ : ∀ (a b : ℕ) (h : ∑ i, ![a, b] i = m + 1), 0 < a → 0 < b →
      ∀ x : π.V, x ∈ twKer π.ρ (unipRad k (stdBlocks ![a, b] h)) 1 := by
    intro a b h ha hb x
    have := Submodule.Quotient.subsingleton_iff.1
      (hcusp.2 2 ![a, b] (stdBlocks ![a, b] h) (GlobalTheory.T.unipRad_stdBlocks_two_ne_bot' k (m + 1) a b h ha hb))
    rw [this]
    exact Submodule.mem_top
  have hJ2 : ∀ (a b : ℕ) (h : ∑ i, ![a, b] i = m + 1), 0 < a → 0 < b →
      ∀ x : π.V, x ∈ twKer (π.ρ.comp (theta k (m + 1))) (unipRad k (stdBlocks ![a, b] h)) 1 := by
    intro a b h ha hb x
    have h' : ∑ i, ![b, a] i = m + 1 := by
      simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at h ⊢
      omega
    refine (Submodule.span_le.2 ?_) (hJ b a h' hb ha x)
    rintro _ ⟨n, y, rfl⟩
    refine Submodule.subset_span ⟨⟨theta k (m + 1) n, ?_⟩, y, ?_⟩
    · rw [theta_apply]
      exact GlobalTheory.T.long_element_conj_unipotent_radical k (m + 1) b a h' h n n.2
    · simp only [MonoidHom.one_apply, Units.val_one, one_smul, MonoidHom.comp_apply]
      rw [theta_theta]
  have hψ'1 : (ψ⁻¹ : AddChar k Circle) ≠ 1 := fun h => hψ1 (inv_eq_one.1 h)
  obtain ⟨C2, hC2, hsupp2⟩ := exists_compact_mod_unipB_whittaker k ψ⁻¹ (continuous_inv_addChar hψc) hψ'1 m π.V
    (π.ρ.comp (theta k (m + 1))) hs2 hJ2 l hl2 (π.ρ (longElt (m + 1) k) v)
  have key : (fun g : GL (Fin m) k => l (π.ρ (tilde (corner g)) v)) =
      fun g => l ((π.ρ.comp (theta k (m + 1))) (corner g) (π.ρ (longElt (m + 1) k) v)) := by
    funext g
    rw [tilde_eq, map_mul, Module.End.mul_apply]
    rfl
  rw [key]
  refine ⟨fun u hu g => ?_, ?_, C2, hC2, hsupp2⟩
  · obtain ⟨h1, h2⟩ := GlobalTheory.T.glCornerEmbedding_upperUnitriangular_superDiagonalSum k m u hu
    beta_reduce
    rw [corner_mul, map_mul, Module.End.mul_apply, hl2 _ h1, h2]
  · exact ((isLocallyConstant_orbit hs2 _).comp_continuous (continuous_corner m)).comp l

end Local

/- English proof (translation)
Introduce `hGen hKir hBig hSep k _ _ _ _ _ ψ hψc hψ1 m hm π₁ π₂ hc₁ hc₂ H`. Establish `hn₁ : Nontrivial π₁.V` using `nontrivial_of_irreducible π₁.irr`. Establish `hn₂ : Nontrivial π₂.V` using `nontrivial_of_irreducible π₂.irr`. Take `⟨l₁, hl₁0, hl₁⟩` from `hGen k ψ hψc hψ1 _ _ π₁.ρ hn₁ hc₁`. Take `⟨l₂, hl₂0, hl₂⟩` from `hGen k ψ hψc hψ1 _ _ π₂.ρ hn₂ hc₂`.

Use `hBig k ψ m hm π₁ π₂ l₁ l₂ hl₁ hl₂ (fun v₁ v₂ hv => ?_) ?_` and prove the remaining obligations. Take `⟨I, hI, hS⟩` from `hSep k m`. Establish `hT` using `(isWhitTest_tilde hψc hψ1 π₁ hc₁ hl₁ v₁).sub (isWhitTest_tilde hψc hψ1 π₂ hc₂ hl₂ v₂)`. Establish `h0` using `hS ψ⁻¹ (continuous_inv_addChar hψc) _ hT fun σ l hl v => by`. Rewrite `hl` using `[inv_inv]`.

Take `⟨e, he₁, he₂⟩` from `H (thetaIrr σ)`. Take `⟨ω, -, hω⟩` from `exists_smooth_hasCentralChar (thetaIrr σ).smooth (thetaIrr σ).irr`. Establish `hl' : IsFunctional ψ⁻¹ (thetaIrr σ).ρ l` using `isFunctional_theta hl`. Establish `e₁` using `he₁ ω hω l₁ l hl₁ hl' I hI v₁ (σ.ρ (theta k m (longElt m k))⁻¹ v)`. Establish `e₂` using `he₂ ω hω l₂ l hl₂ hl' I hI v₂ (σ.ρ (theta k m (longElt m k))⁻¹ v)`.

Establish `ht : ∀ g : GL (Fin m) k, (thetaIrr σ).ρ (tilde g) (σ.ρ (theta k m (longElt m k))⁻¹ v) = σ.ρ g v` using `fun g => by show σ.ρ (theta k m (tilde g)) (σ.ρ (theta k m (longElt m k))⁻¹ v) = σ.ρ g v`. Rewrite using `[tilde_eq, map_mul, theta_theta, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel_right]`. Simplify using `only [ht] at e₁ e₂`. Simplify using `only [hv] at e₁`. Establish `e₃` using `sub_eq_zero.2 (e₁.trans e₂.symm)`.

Rewrite `e₃` using `[← map_sub]`. Rewrite using `[← e₃]`. Use `congr 1`. Use function extensionality and compare the values at `g`. Conclude with `sub_mul _ _ _`.

Establish `h1` using `congrFun h0 1`. Establish `hw : tilde (corner (1 : GL (Fin m) k)) = longElt (m + 1) k`. Rewrite using `[corner_one, tilde_eq, map_one, one_mul]`. Simplify using `only [hw, Pi.zero_apply] at h1`. Conclude with `sub_eq_zero.1 h1`.

Choose the witnesses or unpack the hypotheses as in `⟨a₁, ha₁⟩ : ∃ a, l₁ a = 1 := by`. Take `⟨a, ha⟩` from `DFunLike.ne_iff.1 hl₁0`. Conclude with `⟨(l₁ a)⁻¹ • a, by rw [map_smul, smul_eq_mul, inv_mul_cancel₀ (by simpa using ha)]⟩`. Choose the witnesses or unpack the hypotheses as in `⟨a₂, ha₂⟩ : ∃ a, l₂ a = 1 := by`. Take `⟨a, ha⟩` from `DFunLike.ne_iff.1 hl₂0`.

Conclude with `⟨(l₂ a)⁻¹ • a, by rw [map_smul, smul_eq_mul, inv_mul_cancel₀ (by simpa using ha)]⟩`. Apply the tactic sequence `let ρ : Representation ℂ (GL (Fin (m + 1)) k) (π₁.V × π₂.V) := { toFun := fun g => (π₁.ρ g).prodMap (π₂.ρ g) map_one' := by ext <;> simp map_mul' := fun g h => by ext <;> simp }`. Establish `hρ : ∀ g v, ρ g v = (π₁.ρ g v.1, π₂.ρ g v.2)` using `fun _ _ => rfl`. Establish `hs : IsSmooth ρ` using `fun v => by`. Establish `: {g | ρ g v = v} = {g | π₁.ρ g v.1 = v.1} ∩ {g | π₂.ρ g v.2 = v.2}`.

Use extensionality with `g`. Simplify using `[hρ, Prod.ext_iff]`. Rewrite using `[this]`. Conclude with `(π₁.smooth _).inter (π₂.smooth _)`. Take `⟨v, hv⟩` from `hKir k ψ hψc hψ1 m _ ρ hs (a₁, a₂)`.

Establish `hA` using `(hv (l₁.comp (LinearMap.fst ℂ _ _)) fun u hu x => hl₁ u hu x.1).1`. Establish `hB` using `(hv (l₁.comp (LinearMap.fst ℂ _ _) - l₂.comp (LinearMap.snd ℂ _ _)) fun u hu x => by`. Simplify using `only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.fst_apply, LinearMap.snd_apply, hρ, hl₁ u hu, hl₂ u hu]`. Use the proof step `ring).2 (by simp [ha₁, ha₂])`. Use `⟨v.1, v.2, fun g => sub_eq_zero.1 (hB g), ?_⟩` and prove the remaining obligations.

Establish `: l₁ v.1 = 1` using `hA.trans ha₁`. Rewrite using `[this]`. Conclude with `one_ne_zero`.
-/
theorem glue : Glue := by
  intro hGen hKir hBig hSep k _ _ _ _ _ ψ hψc hψ1 m hm π₁ π₂ hc₁ hc₂ H
  have hn₁ : Nontrivial π₁.V := nontrivial_of_irreducible π₁.irr
  have hn₂ : Nontrivial π₂.V := nontrivial_of_irreducible π₂.irr
  obtain ⟨l₁, hl₁0, hl₁⟩ := hGen k ψ hψc hψ1 _ _ π₁.ρ hn₁ hc₁
  obtain ⟨l₂, hl₂0, hl₂⟩ := hGen k ψ hψc hψ1 _ _ π₂.ρ hn₂ hc₂
  refine hBig k ψ m hm π₁ π₂ l₁ l₂ hl₁ hl₂ (fun v₁ v₂ hv => ?_) ?_
  · obtain ⟨I, hI, hS⟩ := hSep k m
    have hT := (isWhitTest_tilde hψc hψ1 π₁ hc₁ hl₁ v₁).sub (isWhitTest_tilde hψc hψ1 π₂ hc₂ hl₂ v₂)
    have h0 := hS ψ⁻¹ (continuous_inv_addChar hψc) _ hT fun σ l hl v => by
      rw [inv_inv] at hl
      obtain ⟨e, he₁, he₂⟩ := H (thetaIrr σ)
      obtain ⟨ω, -, hω⟩ := exists_smooth_hasCentralChar (thetaIrr σ).smooth (thetaIrr σ).irr
      have hl' : IsFunctional ψ⁻¹ (thetaIrr σ).ρ l := isFunctional_theta hl
      have e₁ := he₁ ω hω l₁ l hl₁ hl' I hI v₁ (σ.ρ (theta k m (longElt m k))⁻¹ v)
      have e₂ := he₂ ω hω l₂ l hl₂ hl' I hI v₂ (σ.ρ (theta k m (longElt m k))⁻¹ v)
      have ht : ∀ g : GL (Fin m) k,
          (thetaIrr σ).ρ (tilde g) (σ.ρ (theta k m (longElt m k))⁻¹ v) = σ.ρ g v := fun g => by
        show σ.ρ (theta k m (tilde g)) (σ.ρ (theta k m (longElt m k))⁻¹ v) = σ.ρ g v
        rw [tilde_eq, map_mul, theta_theta, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel_right]
      simp only [ht] at e₁ e₂
      simp only [hv] at e₁
      have e₃ := sub_eq_zero.2 (e₁.trans e₂.symm)
      rw [← map_sub] at e₃
      rw [← e₃]
      congr 1
      funext g
      exact sub_mul _ _ _
    have h1 := congrFun h0 1
    have hw : tilde (corner (1 : GL (Fin m) k)) = longElt (m + 1) k := by
      rw [corner_one, tilde_eq, map_one, one_mul]
    simp only [hw, Pi.zero_apply] at h1
    exact sub_eq_zero.1 h1
  · obtain ⟨a₁, ha₁⟩ : ∃ a, l₁ a = 1 := by
      obtain ⟨a, ha⟩ := DFunLike.ne_iff.1 hl₁0
      exact ⟨(l₁ a)⁻¹ • a, by rw [map_smul, smul_eq_mul, inv_mul_cancel₀ (by simpa using ha)]⟩
    obtain ⟨a₂, ha₂⟩ : ∃ a, l₂ a = 1 := by
      obtain ⟨a, ha⟩ := DFunLike.ne_iff.1 hl₂0
      exact ⟨(l₂ a)⁻¹ • a, by rw [map_smul, smul_eq_mul, inv_mul_cancel₀ (by simpa using ha)]⟩
    let ρ : Representation ℂ (GL (Fin (m + 1)) k) (π₁.V × π₂.V) :=
      { toFun := fun g => (π₁.ρ g).prodMap (π₂.ρ g)
        map_one' := by ext <;> simp
        map_mul' := fun g h => by ext <;> simp }
    have hρ : ∀ g v, ρ g v = (π₁.ρ g v.1, π₂.ρ g v.2) := fun _ _ => rfl
    have hs : IsSmooth ρ := fun v => by
      have : {g | ρ g v = v} = {g | π₁.ρ g v.1 = v.1} ∩ {g | π₂.ρ g v.2 = v.2} := by
        ext g
        simp [hρ, Prod.ext_iff]
      rw [this]
      exact (π₁.smooth _).inter (π₂.smooth _)
    obtain ⟨v, hv⟩ := hKir k ψ hψc hψ1 m _ ρ hs (a₁, a₂)
    have hA := (hv (l₁.comp (LinearMap.fst ℂ _ _)) fun u hu x => hl₁ u hu x.1).1
    have hB := (hv (l₁.comp (LinearMap.fst ℂ _ _) - l₂.comp (LinearMap.snd ℂ _ _)) fun u hu x => by
      simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.fst_apply, LinearMap.snd_apply, hρ,
        hl₁ u hu, hl₂ u hu]
      ring).2 (by simp [ha₁, ha₂])
    refine ⟨v.1, v.2, fun g => sub_eq_zero.1 (hB g), ?_⟩
    have : l₁ v.1 = 1 := hA.trans ha₁
    rw [this]
    exact one_ne_zero

end DiscreteGroups.sglob.LConv

end
