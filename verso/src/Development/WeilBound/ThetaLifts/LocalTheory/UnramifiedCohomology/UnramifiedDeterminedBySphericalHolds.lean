import Development.WeilBound.ThetaLifts.LocalTheory.UnramifiedMultiplicityOneProportional
import Development.WeilBound.ThetaLifts.LocalTheory.UnramifiedCohomology.MemLatWIff
import Development.WeilBound.ThetaLifts.TowerModels.LeviAd
import Development.WeilBound.CoreStatements.LocalThetaKernels.Locrep
import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.Vaceigen

noncomputable section

namespace PositivityTheory.ThKG.Loc

open scoped TensorProduct NNReal Matrix nonZeroDivisors
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK PositivityTheory.ThKH.Iwas PositivityTheory.ThKG.Tow.Levi
open GlobalTheory.Doubling (absE)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

variable {B : Base F E} {d d₁ : ℕ} {W : Spc F E d} {W₁ : Spc F E d₁} {H : Plane E d d₁} {i₀ i₁ r s : ℕ} {v : Pl F}

/- English proof (translation)
Establish `hd : IsUnit W₁.J.det` using `(isFr hB hW hH).isUnit_det (PositivityTheory.ThKG.Tow.Levi.det_ne_zero hW).isUnit`. Establish `hF` using `isFrA hB hW hH`. Take `⟨g, α, hg, hα⟩` from `hF.stab t.mul_inv p.2 ht`. Establish `hgu : IsUnit g.det`. Establish `e` using `congrArg Matrix.det hg`.

Establish `hd' : IsUnit (incM F W₁.J).det`. Use `hd.map (inclR (F := F) (AF F))` as an intermediate fact. Rewrite `this` using `[RingHom.map_det]`. Then use the resulting hypothesis. Rewrite `hd'` using `[← e, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]`. Conclude with `isUnit_of_mul_isUnit_left (isUnit_of_mul_isUnit_left hd')`.

Use `replace hα : ∀ z, mat p *ᵥ (incM F H.ι *ᵥ z) = incM F H.ι *ᵥ (g *ᵥ z) + (α ⬝ᵥ z) • incV F H.x := hα`. Take `⟨h₁, rfl⟩` from `exists_UA (σ := σ) (Matrix.mul_nonsing_inv _ hgu) hg`. Take `⟨m, hm⟩` from `exists_levi hB hW hH t h₁`. Take `⟨A', a1, a2⟩` from `hF.inv`. Use `set A := fr (incM F H.ι) (incV F H.x) (incV F H.y) with hA`.

Establish `cx : A *ᵥ Pi.single (Sum.inr 0) 1 = incV F H.x` using `by ext i; simp [hA, fr]`. Establish `cy : A *ᵥ Pi.single (Sum.inr 1) 1 = incV F H.y` using `by ext i; simp [hA, fr]`. Establish `ci : ∀ z, A *ᵥ Sum.elim z 0 = incM F H.ι *ᵥ z` using `fun z => by rw [hA, fr, Matrix.fromCols_mulVec_sumElim]; simp`. Establish `inj : ∀ z, A *ᵥ z = 0 → z = 0` using `fun z h => by`. Rewrite using `[← Matrix.one_mulVec z, ← a2, ← Matrix.mulVec_mulVec, h, Matrix.mulVec_zero]`.

Establish `pa : ∀ a : AF F, evFin F v a = 0 → ∀ z, a • (mat p *ᵥ z) = a • z` using `fun a ha z => by`. Use `congrArg (· *ᵥ z) (hp a ha)` as an intermediate fact. Simplify `this` using `only [Matrix.smul_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.zero_mulVec, smul_sub, sub_eq_zero]`. Establish `t1 : ∀ a : AF F, evFin F v a = 0 → a • t.1 = a • 1` using `fun a ha => by`. Establish `h` using `pa a ha (incV F H.x)`.

Rewrite `h` using `[ht, ← cx, ← Matrix.mulVec_smul, ← Matrix.mulVec_smul, ← Matrix.mulVec_smul, ← sub_eq_zero, ← Matrix.mulVec_sub]`. Use `congrFun (inj _ h) (Sum.inr 0)` as an intermediate fact. Simplify `this` using `[sub_eq_zero]`. Establish `t2 : ∀ a : AF F, evFin F v a = 0 → a • cA σ (t⁻¹).1 = a • 1` using `fun a ha => by`. Establish `: a • (t⁻¹).1 = a • 1`.

Establish `q` using `congrArg ((t⁻¹).1 * ·) (t1 a ha)`. Simplify using `only [mul_smul_comm, Units.inv_mul, mul_one] at q`. Conclude with `q.symm`. Rewrite using `[← map_smul, this, map_smul, map_one]`. Establish `g1 : ∀ a : AF F, evFin F v a = 0 → ∀ z, a • (mat h₁ *ᵥ z) = a • z` using `fun a ha z => by`.

Establish `h` using `pa a ha (incM F H.ι *ᵥ z)`. Rewrite `h` using `[hα, ← ci, ← ci, ← cx, ← Matrix.mulVec_smul, ← Matrix.mulVec_add, ← Matrix.mulVec_smul, ← Matrix.mulVec_smul, ← sub_eq_zero, ← Matrix.mulVec_sub]`. Use function extensionality and compare the values at `j`. Use `congrFun (inj _ h) (Sum.inl j)` as an intermediate fact. Simplify `this` using `[sub_eq_zero]`.

Establish `ofv : ∀ {k : ℕ} (M : Matrix (Fin k) (Fin k) (AE F E)), (∀ a : AF F, evFin F v a = 0 → ∀ z, a • (M *ᵥ z) = a • z) → At (evFin F v) (M - 1)` using `fun M h a ha => by`. Use `Matrix.ext_iff_mulVec.2 fun z => ?_` and prove the remaining obligations. Rewrite using `[Matrix.smul_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.zero_mulVec, smul_sub, h a ha, sub_self]`. Establish `hm' : m ∈ USub σ W v` using `ofv _ fun a ha z => by`. Take `⟨w, rfl⟩ : ∃ w, z = A *ᵥ w` from `⟨A' *ᵥ z, by rw [Matrix.mulVec_mulVec, a1, Matrix.one_mulVec]⟩`.

Establish `e : A *ᵥ w = incM F H.ι *ᵥ (fun j => w (.inl j)) + w (.inr 0) • incV F H.x + w (.inr 1) • incV F H.y`. Rewrite using `[← ci, ← cx, ← cy, ← Matrix.mulVec_smul, ← Matrix.mulVec_smul, ← Matrix.mulVec_add, ← Matrix.mulVec_add]`. Use `congr 1`. Use extensionality with `(j | j)`. Simplify using the standard rewrite rules.

Apply the tactic sequence `fin_cases j <;> simp`. Rewrite using `[e, Matrix.mulVec_add, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, hm.1, hm.2.1, Matrix.mulVec_mulVec, hm.2.2, ← Matrix.mulVec_mulVec]`. Simplify using `only [smul_add]`. Rewrite using `[← Matrix.mulVec_smul, g1 a ha, Matrix.mulVec_smul, smul_comm a (w _), smul_comm a (w _), smul_comm a (w _), smul_comm a (w _), ← smul_assoc a t.1, ← smul_assoc a (cA σ _), t1 a ha, t2 a ha, smul_assoc, smul_assoc, one_smul, one_smul]`. Use `⟨h₁, ofv _ g1, m, hm', hm, p * m⁻¹, Subgroup.subset_closure ?_, mul_mem (show p ∈ USub σ W v from hp) (inv_mem hm'), by group⟩` and prove the remaining obligations.

Take `⟨u, hu⟩ : ∃ u, u = p * m⁻¹` from `⟨_, rfl⟩`. Establish `e : mat u * mat m = mat p`. Rewrite using `[hu]`. Conclude with `congrArg mat (inv_mul_cancel_right p m)`. Rewrite using `[← hu]`.

Prove the components needed by the constructor for the conclusion. Establish `e1 : t.1 • (mat u *ᵥ incV F H.x) = t.1 • incV F H.x`. Rewrite using `[← ht, ← e, ← Matrix.mulVec_mulVec, hm.1, Matrix.mulVec_smul]`. Conclude with `(t.isUnit.smul_left_cancel).1 e1`. Introduce `z`.

Take `⟨y, rfl⟩ : ∃ y, z = mat h₁ *ᵥ y` from `⟨mat h₁⁻¹ *ᵥ z, by rw [Matrix.mulVec_mulVec, show mat h₁ * mat h₁⁻¹ = 1 from h₁.1.mul_inv, Matrix.one_mulVec]⟩`. Use `⟨α ⬝ᵥ y, ?_⟩` and prove the remaining obligations. Establish `e2 : mat u * (incM F H.ι * mat h₁) = mat p * incM F H.ι` using `by rw [← e, Matrix.mul_assoc, hm.2.2]`. Rewrite using `[← hα, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc, e2]`.
-/
theorem parDec (hB : B.IsGood σ) (hW : W.IsSkew σ B r s) (hH : H.IsAdapted σ B W W₁ i₀ i₁) {p : UA σ W.J}
    (hp : p ∈ UAt σ W (evFin F v)) {t : (AE F E)ˣ} (ht : mat p *ᵥ incV F H.x = t.1 • incV F H.x) :
    ∃ h₁ ∈ UAt σ W₁ (evFin F v), ∃ m ∈ UAt σ W (evFin F v), IsLevi H t h₁ m ∧ ∃ u ∈ unip σ W H, u ∈ UAt σ W (evFin F v) ∧
      p = u * m := by
  have hd : IsUnit W₁.J.det := (isFr hB hW hH).isUnit_det (PositivityTheory.ThKG.Tow.Levi.det_ne_zero hW).isUnit
  have hF := isFrA hB hW hH
  obtain ⟨g, α, hg, hα⟩ := hF.stab t.mul_inv p.2 ht
  have hgu : IsUnit g.det := by
    have e := congrArg Matrix.det hg
    have hd' : IsUnit (incM F W₁.J).det := by
      have := hd.map (inclR (F := F) (AF F))
      rwa [RingHom.map_det] at this
    rw [← e, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose] at hd'
    exact isUnit_of_mul_isUnit_left (isUnit_of_mul_isUnit_left hd')
  replace hα : ∀ z, mat p *ᵥ (incM F H.ι *ᵥ z) = incM F H.ι *ᵥ (g *ᵥ z) + (α ⬝ᵥ z) • incV F H.x := hα
  obtain ⟨h₁, rfl⟩ := exists_UA (σ := σ) (Matrix.mul_nonsing_inv _ hgu) hg
  obtain ⟨m, hm⟩ := exists_levi hB hW hH t h₁
  obtain ⟨A', a1, a2⟩ := hF.inv
  set A := fr (incM F H.ι) (incV F H.x) (incV F H.y) with hA
  have cx : A *ᵥ Pi.single (Sum.inr 0) 1 = incV F H.x := by ext i; simp [hA, fr]
  have cy : A *ᵥ Pi.single (Sum.inr 1) 1 = incV F H.y := by ext i; simp [hA, fr]
  have ci : ∀ z, A *ᵥ Sum.elim z 0 = incM F H.ι *ᵥ z := fun z => by rw [hA, fr, Matrix.fromCols_mulVec_sumElim]; simp
  have inj : ∀ z, A *ᵥ z = 0 → z = 0 := fun z h => by
    rw [← Matrix.one_mulVec z, ← a2, ← Matrix.mulVec_mulVec, h, Matrix.mulVec_zero]
  have pa : ∀ a : AF F, evFin F v a = 0 → ∀ z, a • (mat p *ᵥ z) = a • z := fun a ha z => by
    have := congrArg (· *ᵥ z) (hp a ha)
    simpa only [Matrix.smul_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.zero_mulVec, smul_sub, sub_eq_zero] using this
  have t1 : ∀ a : AF F, evFin F v a = 0 → a • t.1 = a • 1 := fun a ha => by
    have h := pa a ha (incV F H.x)
    rw [ht, ← cx, ← Matrix.mulVec_smul, ← Matrix.mulVec_smul, ← Matrix.mulVec_smul, ← sub_eq_zero, ← Matrix.mulVec_sub] at h
    have := congrFun (inj _ h) (Sum.inr 0)
    simpa [sub_eq_zero] using this
  have t2 : ∀ a : AF F, evFin F v a = 0 → a • cA σ (t⁻¹).1 = a • 1 := fun a ha => by
    have : a • (t⁻¹).1 = a • 1 := by
      have q := congrArg ((t⁻¹).1 * ·) (t1 a ha)
      simp only [mul_smul_comm, Units.inv_mul, mul_one] at q
      exact q.symm
    rw [← map_smul, this, map_smul, map_one]
  have g1 : ∀ a : AF F, evFin F v a = 0 → ∀ z, a • (mat h₁ *ᵥ z) = a • z := fun a ha z => by
    have h := pa a ha (incM F H.ι *ᵥ z)
    rw [hα, ← ci, ← ci, ← cx, ← Matrix.mulVec_smul, ← Matrix.mulVec_add, ← Matrix.mulVec_smul, ← Matrix.mulVec_smul,
      ← sub_eq_zero, ← Matrix.mulVec_sub] at h
    funext j
    have := congrFun (inj _ h) (Sum.inl j)
    simpa [sub_eq_zero] using this
  have ofv : ∀ {k : ℕ} (M : Matrix (Fin k) (Fin k) (AE F E)), (∀ a : AF F, evFin F v a = 0 → ∀ z, a • (M *ᵥ z) = a • z) →
      At (evFin F v) (M - 1) := fun M h a ha => by
    refine Matrix.ext_iff_mulVec.2 fun z => ?_
    rw [Matrix.smul_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.zero_mulVec, smul_sub, h a ha, sub_self]
  have hm' : m ∈ USub σ W v := ofv _ fun a ha z => by
    obtain ⟨w, rfl⟩ : ∃ w, z = A *ᵥ w := ⟨A' *ᵥ z, by rw [Matrix.mulVec_mulVec, a1, Matrix.one_mulVec]⟩
    have e : A *ᵥ w = incM F H.ι *ᵥ (fun j => w (.inl j)) + w (.inr 0) • incV F H.x + w (.inr 1) • incV F H.y := by
      rw [← ci, ← cx, ← cy, ← Matrix.mulVec_smul, ← Matrix.mulVec_smul, ← Matrix.mulVec_add, ← Matrix.mulVec_add]
      congr 1
      ext (j | j)
      · simp
      · fin_cases j <;> simp
    rw [e, Matrix.mulVec_add, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, hm.1, hm.2.1, Matrix.mulVec_mulVec,
      hm.2.2, ← Matrix.mulVec_mulVec]
    simp only [smul_add]
    rw [← Matrix.mulVec_smul, g1 a ha, Matrix.mulVec_smul, smul_comm a (w _), smul_comm a (w _), smul_comm a (w _),
      smul_comm a (w _), ← smul_assoc a t.1, ← smul_assoc a (cA σ _), t1 a ha, t2 a ha, smul_assoc, smul_assoc, one_smul,
      one_smul]
  refine ⟨h₁, ofv _ g1, m, hm', hm, p * m⁻¹, Subgroup.subset_closure ?_, mul_mem (show p ∈ USub σ W v from hp) (inv_mem hm'),
    by group⟩
  obtain ⟨u, hu⟩ : ∃ u, u = p * m⁻¹ := ⟨_, rfl⟩
  have e : mat u * mat m = mat p := by
    rw [hu]; exact congrArg mat (inv_mul_cancel_right p m)
  rw [← hu]
  constructor
  · have e1 : t.1 • (mat u *ᵥ incV F H.x) = t.1 • incV F H.x := by
      rw [← ht, ← e, ← Matrix.mulVec_mulVec, hm.1, Matrix.mulVec_smul]
    exact (t.isUnit.smul_left_cancel).1 e1
  · intro z
    obtain ⟨y, rfl⟩ : ∃ y, z = mat h₁ *ᵥ y :=
      ⟨mat h₁⁻¹ *ᵥ z, by rw [Matrix.mulVec_mulVec, show mat h₁ * mat h₁⁻¹ = 1 from h₁.1.mul_inv, Matrix.one_mulVec]⟩
    refine ⟨α ⬝ᵥ y, ?_⟩
    have e2 : mat u * (incM F H.ι * mat h₁) = mat p * incM F H.ι := by rw [← e, Matrix.mul_assoc, hm.2.2]
    rw [← hα, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc, e2]

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ B a a' a₁ a₁' G G₁ X om om' om₁ om₁' R Rf R₁ Rf₁ H' i₀ i₁ χ r hM hM₁ _ hH v hv l₁ l₂ hl₁ hl₂ c₀ h0`. Take `⟨lam, hlam⟩ : ∃ lam, lam = l₂ - c₀ • l₁` from `⟨_, rfl⟩`. It suffices to establish `lam = 0 from sub_eq_zero.1 (hlam ▸ this)`. Establish `T` using `hM.triple`. Establish `T₁` using `hM₁.triple`.

Establish `P : PositivityTheory.ThK.PairOK B G.V G.W G.M om` using `⟨T.base, ⟨_, _, T.geo.hV⟩, ⟨_, _, T.geo.hW⟩, T.geo.hM, _, _, T.weil⟩`. Establish `P' : PositivityTheory.ThK.PairOK B G.V' G.W G.M' om'` using `⟨T.base, ⟨_, _, T.geo.hV'⟩, ⟨_, _, T.geo.hW⟩, T.geo.hM', _, _, T.weil'⟩`. Establish `P₁ : PositivityTheory.ThK.PairOK B G₁.V G₁.W G₁.M om₁` using `⟨T₁.base, ⟨_, _, T₁.geo.hV⟩, ⟨_, _, T₁.geo.hW⟩, T₁.geo.hM, _, _, T₁.weil⟩`. Take `⟨ω, ρ, L⟩` from `PositivityTheory.ThKH.Locrep.locRepEx F E σ _ _ B _ _ _ _ P v`. Take `⟨ω', ρ', L'⟩` from `PositivityTheory.ThKH.Locrep.locRepEx F E σ _ _ B _ _ _ _ P' v`.

Take `⟨ω₁, ρ₁, L₁⟩` from `PositivityTheory.ThKH.Locrep.locRepEx F E σ _ _ B _ _ _ _ P₁ v`. Establish `o : (1 : UA σ G.V.J) ∈ UAt σ G.V (evFin F v)` using `(USub σ G.V v).one_mem`. Establish `o' : (1 : UA σ G.V'.J) ∈ UAt σ G.V' (evFin F v)` using `(USub σ G.V' v).one_mem`. Establish `o₁ : (1 : UA σ G₁.V.J) ∈ UAt σ G₁.V (evFin F v)` using `(USub σ G₁.V v).one_mem`. Establish `hvac` using `(T.geo.hM.vac v).1`.

Establish `ker : ∀ h ∈ UAt σ G.W (evFin F v), ∀ φ ∈ SB _, Rf.p v φ = 0 → Rf.p v (ω (1, h) φ) = 0` using `fun h hh φ hφ e => by`. Use `hM.fin.equiv v h hh φ hφ 0 (zero_mem _) _ (L.pres 1 o h hh φ hφ) _ (L'.pres 1 o' h hh 0 (zero_mem _)) ((L.acts 1 o h hh φ hφ _).2 rfl) ((L'.acts 1 o' h hh 0 (zero_mem _) _).2 rfl) (by rw [e, map_zero])` as an intermediate fact. Rewrite using `[this, map_zero, map_zero]`. Set `S : Submodule ℂ (Fl F v a (a + a'))` to `SB _ ⊓ ⨅ h ∈ UAt σ G.W (evFin F v), LinearMap.ker (lam ∘ₗ Rf.p v ∘ₗ ω (1, h))`. Establish `mS : ∀ φ, φ ∈ S ↔ φ ∈ SB _ ∧ ∀ h ∈ UAt σ G.W (evFin F v), lam (Rf.p v (ω (1, h) φ)) = 0` using `fun φ => by`.

Simplify using `[S, Submodule.mem_iInf]`. Establish `hS : G.M.vac v ∈ S` using `(mS _).2 ⟨hvac, fun h hh => by`. Establish `hx : H'.x ≠ 0` using `fun e => by simpa [e, form] using hH.xy`. Take `⟨p, hp, k, hk, t, ht, rfl⟩` from `Iwa.iwaLoc T.base (.inr T.geo.hW) hx hH.xx v hh`. Take `⟨h₁, hh₁, m, hm, hL, u, hu, hu', rfl⟩` from `parDec T.base T.geo.hW hH hp ht`.

Take `⟨c, hc⟩` from `PositivityTheory.ThK.vacuum_eigenline_of_local PositivityTheory.ThKH.Locrep.locRepEx F E σ _ _ B _ _ _ _ P v k hk`. Establish `e` using `L.mul 1 o _ hp 1 o k hk.1 _ hvac`. Rewrite `e` using `[mul_one, ← (L.acts 1 o k hk.1 _ hvac _).1 hc, map_smul]`. Take `⟨b, hb, eb⟩ : l₁ (Rf.p v (G.M.vac v)) ∈ (SB _).map (Rf₁.p v)` from `hM₁.fin.onto v ▸ Submodule.mem_top`. Establish `hcb` using `Submodule.smul_mem _ c₀ hb`.

Establish `q₁` using `hl₁ t h₁ m hL u hu hu' hm _ hvac _ (L.pres 1 o _ hp _ hvac) b hb _ (L₁.pres 1 o₁ h₁ hh₁ b hb) ((L.acts 1 o _ hp _ hvac _).2 rfl) ((L₁.acts 1 o₁ h₁ hh₁ b hb _).2 rfl) eb.symm`. Establish `q₂` using `hl₂ t h₁ m hL u hu hu' hm _ hvac _ (L.pres 1 o _ hp _ hvac) _ hcb _ (L₁.pres 1 o₁ h₁ hh₁ _ hcb) ((L.acts 1 o _ hp _ hvac _).2 rfl) ((L₁.acts 1 o₁ h₁ hh₁ _ hcb _).2 rfl) (by rw [h0, map_smul, eb])`. Rewrite using `[e, map_smul, map_smul, hlam, LinearMap.sub_apply, LinearMap.smul_apply, q₁, q₂, map_smul, map_smul, smul_comm c₀, sub_self, smul_zero]⟩`. Establish `hN` using `hM.fin.irred v (S.map (Rf.p v)) (fun h hh φ hφ φ₁ _ hA ⟨ψ, hψ, e⟩ => by`. Take `⟨hψ1, hψ2⟩` from `(mS ψ).1 hψ`.

Rewrite using `[(L.acts 1 o h hh φ hφ _).1 hA]`. Use `⟨ω (1, h) ψ, (mS _).2 ⟨L.pres 1 o h hh ψ hψ1, fun h' hh' => ?_⟩, ?_⟩` and prove the remaining obligations. Use `L.mul 1 o h' hh' 1 o h hh ψ hψ1` as an intermediate fact. Rewrite `this` using `[mul_one]`. Rewrite using `[← this]`.

Conclude with `hψ2 _ ((USub σ G.W v).mul_mem hh' hh)`. Use `ker h hh _ (sub_mem hψ1 hφ) (by rw [map_sub, e, sub_self])` as an intermediate fact. Rewrite using `[map_sub, map_sub, sub_eq_zero] at this)` and apply the resulting hypothesis. Break down `hN with hN | hN` into its components or cases. Conclude with `absurd ((Submodule.eq_bot_iff _).1 hN _ ⟨_, hS, rfl⟩) (hM.fin.sph v hv).2`.

Use `LinearMap.ext fun ξ => ?_` and prove the remaining obligations. Take `⟨ψ, hψ, rfl⟩ : ξ ∈ S.map (Rf.p v)` from `hN ▸ Submodule.mem_top`. Take `⟨h1, h2⟩` from `(mS ψ).1 hψ`. Use `h2 1 (USub σ G.W v).one_mem` as an intermediate fact. Rewrite `this` using `[show ((1 : UA σ G.V.J), (1 : UA σ G.W.J)) = 1 from rfl, L.one ψ h1]`. Then use the resulting hypothesis.
-/
theorem unramifiedProportional_holds : UnramifiedMultiplicityOneProportional := by
  intro F E _ _ _ _ _ σ B a a' a₁ a₁' G G₁ X om om' om₁ om₁' R Rf R₁ Rf₁ H' i₀ i₁ χ r hM hM₁ _ hH v hv l₁ l₂ hl₁ hl₂ c₀ h0
  obtain ⟨lam, hlam⟩ : ∃ lam, lam = l₂ - c₀ • l₁ := ⟨_, rfl⟩
  suffices lam = 0 from sub_eq_zero.1 (hlam ▸ this)
  have T := hM.triple
  have T₁ := hM₁.triple
  have P : PositivityTheory.ThK.PairOK B G.V G.W G.M om := ⟨T.base, ⟨_, _, T.geo.hV⟩, ⟨_, _, T.geo.hW⟩, T.geo.hM, _, _, T.weil⟩
  have P' : PositivityTheory.ThK.PairOK B G.V' G.W G.M' om' := ⟨T.base, ⟨_, _, T.geo.hV'⟩, ⟨_, _, T.geo.hW⟩, T.geo.hM', _, _, T.weil'⟩
  have P₁ : PositivityTheory.ThK.PairOK B G₁.V G₁.W G₁.M om₁ := ⟨T₁.base, ⟨_, _, T₁.geo.hV⟩, ⟨_, _, T₁.geo.hW⟩, T₁.geo.hM, _, _, T₁.weil⟩
  obtain ⟨ω, ρ, L⟩ := PositivityTheory.ThKH.Locrep.locRepEx F E σ _ _ B _ _ _ _ P v
  obtain ⟨ω', ρ', L'⟩ := PositivityTheory.ThKH.Locrep.locRepEx F E σ _ _ B _ _ _ _ P' v
  obtain ⟨ω₁, ρ₁, L₁⟩ := PositivityTheory.ThKH.Locrep.locRepEx F E σ _ _ B _ _ _ _ P₁ v
  have o : (1 : UA σ G.V.J) ∈ UAt σ G.V (evFin F v) := (USub σ G.V v).one_mem
  have o' : (1 : UA σ G.V'.J) ∈ UAt σ G.V' (evFin F v) := (USub σ G.V' v).one_mem
  have o₁ : (1 : UA σ G₁.V.J) ∈ UAt σ G₁.V (evFin F v) := (USub σ G₁.V v).one_mem
  have hvac := (T.geo.hM.vac v).1
  have ker : ∀ h ∈ UAt σ G.W (evFin F v), ∀ φ ∈ SB _, Rf.p v φ = 0 → Rf.p v (ω (1, h) φ) = 0 := fun h hh φ hφ e => by
    have := hM.fin.equiv v h hh φ hφ 0 (zero_mem _) _ (L.pres 1 o h hh φ hφ) _ (L'.pres 1 o' h hh 0 (zero_mem _))
      ((L.acts 1 o h hh φ hφ _).2 rfl) ((L'.acts 1 o' h hh 0 (zero_mem _) _).2 rfl) (by rw [e, map_zero])
    rw [this, map_zero, map_zero]
  let S : Submodule ℂ (Fl F v a (a + a')) := SB _ ⊓ ⨅ h ∈ UAt σ G.W (evFin F v), LinearMap.ker (lam ∘ₗ Rf.p v ∘ₗ ω (1, h))
  have mS : ∀ φ, φ ∈ S ↔ φ ∈ SB _ ∧ ∀ h ∈ UAt σ G.W (evFin F v), lam (Rf.p v (ω (1, h) φ)) = 0 := fun φ => by
    simp [S, Submodule.mem_iInf]
  have hS : G.M.vac v ∈ S := (mS _).2 ⟨hvac, fun h hh => by
    have hx : H'.x ≠ 0 := fun e => by simpa [e, form] using hH.xy
    obtain ⟨p, hp, k, hk, t, ht, rfl⟩ := Iwa.iwaLoc T.base (.inr T.geo.hW) hx hH.xx v hh
    obtain ⟨h₁, hh₁, m, hm, hL, u, hu, hu', rfl⟩ := parDec T.base T.geo.hW hH hp ht
    obtain ⟨c, hc⟩ := PositivityTheory.ThK.vacuum_eigenline_of_local PositivityTheory.ThKH.Locrep.locRepEx F E σ _ _ B _ _ _ _ P v k hk
    have e := L.mul 1 o _ hp 1 o k hk.1 _ hvac
    rw [mul_one, ← (L.acts 1 o k hk.1 _ hvac _).1 hc, map_smul] at e
    obtain ⟨b, hb, eb⟩ : l₁ (Rf.p v (G.M.vac v)) ∈ (SB _).map (Rf₁.p v) := hM₁.fin.onto v ▸ Submodule.mem_top
    have hcb := Submodule.smul_mem _ c₀ hb
    have q₁ := hl₁ t h₁ m hL u hu hu' hm _ hvac _ (L.pres 1 o _ hp _ hvac) b hb _
      (L₁.pres 1 o₁ h₁ hh₁ b hb) ((L.acts 1 o _ hp _ hvac _).2 rfl) ((L₁.acts 1 o₁ h₁ hh₁ b hb _).2 rfl) eb.symm
    have q₂ := hl₂ t h₁ m hL u hu hu' hm _ hvac _ (L.pres 1 o _ hp _ hvac) _ hcb _
      (L₁.pres 1 o₁ h₁ hh₁ _ hcb) ((L.acts 1 o _ hp _ hvac _).2 rfl) ((L₁.acts 1 o₁ h₁ hh₁ _ hcb _).2 rfl)
      (by rw [h0, map_smul, eb])
    rw [e, map_smul, map_smul, hlam, LinearMap.sub_apply, LinearMap.smul_apply, q₁, q₂, map_smul, map_smul, smul_comm c₀,
      sub_self, smul_zero]⟩
  have hN := hM.fin.irred v (S.map (Rf.p v)) (fun h hh φ hφ φ₁ _ hA ⟨ψ, hψ, e⟩ => by
    obtain ⟨hψ1, hψ2⟩ := (mS ψ).1 hψ
    rw [(L.acts 1 o h hh φ hφ _).1 hA]
    refine ⟨ω (1, h) ψ, (mS _).2 ⟨L.pres 1 o h hh ψ hψ1, fun h' hh' => ?_⟩, ?_⟩
    · have := L.mul 1 o h' hh' 1 o h hh ψ hψ1
      rw [mul_one] at this
      rw [← this]
      exact hψ2 _ ((USub σ G.W v).mul_mem hh' hh)
    · have := ker h hh _ (sub_mem hψ1 hφ) (by rw [map_sub, e, sub_self])
      rwa [map_sub, map_sub, sub_eq_zero] at this)
  rcases hN with hN | hN
  · exact absurd ((Submodule.eq_bot_iff _).1 hN _ ⟨_, hS, rfl⟩) (hM.fin.sph v hv).2
  · refine LinearMap.ext fun ξ => ?_
    obtain ⟨ψ, hψ, rfl⟩ : ξ ∈ S.map (Rf.p v) := hN ▸ Submodule.mem_top
    obtain ⟨h1, h2⟩ := (mS ψ).1 hψ
    have := h2 1 (USub σ G.W v).one_mem
    rwa [show ((1 : UA σ G.V.J), (1 : UA σ G.W.J)) = 1 from rfl, L.one ψ h1] at this

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ B a a' a₁ a₁' G G₁ X om om' om₁ om₁' R Rf R₁ Rf₁ H' i₀ i₁ χ r hM hM₁ hs hH v hv lam hl h0` and use `by simpa using unramifiedProportional_holds F E σ B a a' a₁ a₁' G G₁ X om om' om₁ om₁' R Rf R₁ Rf₁ H' i₀ i₁ χ r hM hM₁ hs hH v hv lam lam hl hl 0 (by rw [h0, zero_smul])`.
-/
theorem unramifiedDeterminedBySpherical_holds : UnramifiedDeterminedBySpherical := fun F E _ _ _ _ _ σ B a a' a₁ a₁' G G₁ X om om' om₁ om₁' R Rf R₁ Rf₁ H' i₀ i₁ χ r hM hM₁ hs hH v hv
    lam hl h0 => by
  simpa using unramifiedProportional_holds F E σ B a a' a₁ a₁' G G₁ X om om' om₁ om₁' R Rf R₁ Rf₁ H' i₀ i₁ χ r hM hM₁ hs hH v hv lam lam hl hl 0
    (by rw [h0, zero_smul])

end PositivityTheory.ThKG.Loc

end
