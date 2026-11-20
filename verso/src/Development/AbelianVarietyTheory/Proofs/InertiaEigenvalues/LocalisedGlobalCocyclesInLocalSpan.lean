import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LenCob

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass GlobalTheory.Cut

namespace GlobalTheory.Cut.LocCoc

/- English proof (translation)
Set `e` to `(Fintype.equivFin ({x // P x} × Fin n)).symm`. Set `L : (X → Matrix (Fin n) (Fin n) O) →ₗ[O] (Fin (Fintype.card ({x // P x} × Fin n)) → Fin n → K)` to `{ toFun := fun z j s => algebraMap O K (z (e j).1.1 s (e j).2) map_add' := fun a b => by funext j s; simp map_smul' := fun c a => by funext j s; simp [Algebra.smul_def] }`. Establish `key : ∀ (γ : Γ) (z : X → Matrix (Fin n) (Fin n) O), (fun j => (mapM (algebraMap O K) (A (e j).1.1) γ).mulVec (L z j)) = L ((fun x => A x γ) * z)`. Introduce `γ z`. Use function extensionality and compare the values at `j s`.

Use `show ∑ t, algebraMap O K (A (e j).1.1 γ s t) * algebraMap O K (z (e j).1.1 t (e j).2) = algebraMap O K (∑ t, A (e j).1.1 γ s t * z (e j).1.1 t (e j).2)`. Simplify using the standard rewrite rules. Set `Y0` to `Submodule.span O (Set.range y)`. Establish `hmul : ∀ γ δ, (fun x => A x γ) * y δ = y (γ * δ) - y γ`. Introduce `γ δ`.

Use function extensionality and compare the values at `x`. Simplify using `only [Pi.mul_apply, Pi.sub_apply, hy, map_mul]`. Use `noncomm_ring`. Establish `hst0 : ∀ γ, ∀ z ∈ Y0, (fun x => A x γ) * z ∈ Y0 ∧ φ ((fun x => A x γ) * z) = ρ γ (φ z)`. Introduce `γ z hz`.

Proceed by induction on `hz using Submodule.span_induction with`. Consider the case `mem z hz`. Take `⟨δ, rfl⟩` from `hz`. Use `⟨?_, h1 γ δ⟩` and prove the remaining obligations. Rewrite using `[hmul]`.

Conclude with `Y0.sub_mem (Submodule.subset_span ⟨_, rfl⟩) (Submodule.subset_span ⟨_, rfl⟩)`. Consider the case `zero => simp`. Consider the case `add a b _ _ ha hb`. Rewrite using `[mul_add, map_add, map_add, map_add, ha.2, hb.2]`. Conclude with `⟨Y0.add_mem ha.1 hb.1, rfl⟩`.

Consider the case `smul c a _ ha`. Rewrite using `[mul_smul_comm, map_smul, map_smul, map_smul, ha.2]`. Conclude with `⟨Y0.smul_mem c ha.1, rfl⟩`. Establish `hLE : ∀ γ, (fun j => (mapM (algebraMap O K) (A (e j).1.1) γ).mulVec (L E j) - L E j) = L (y γ)`. Introduce `γ`.

Establish `: y γ = (fun x => A x γ) * E - E`. Use function extensionality and compare the values at `x`. Simplify using `[hy, sub_mul]`. Rewrite using `[this, map_sub, ← key]`. Both sides reduce to the same expression.

Set `L0` to `L.domRestrict Y0`. Establish `hker : LinearMap.ker L0 ≤ LinearMap.ker (φ.domRestrict Y0)`. Introduce `z hz`. Use `h0 z.1 z.2 fun x hx => ?_` and prove the remaining obligations. Use extensionality with `s t`.

Apply `hinj` to reduce the goal to its premises. Use `congrFun (congrFun (LinearMap.mem_ker.mp hz) (e.symm (⟨x, hx⟩, t))) s` as an intermediate fact. Simplify `this` using `[L0, L]`. Set `φ' : ↥(LinearMap.range L0) →ₗ[O] W` to `((LinearMap.ker L0).liftQ (φ.domRestrict Y0) hker) ∘ₗ (L0.quotKerEquivRange.symm : _ →ₗ[O] _)`. Establish `hφ' : ∀ (z : Y0) (h : L z.1 ∈ LinearMap.range L0), φ' ⟨L z.1, h⟩ = φ z.1`.

Introduce `z h`. Establish `: L0.quotKerEquivRange.symm ⟨L z.1, h⟩ = (LinearMap.ker L0).mkQ z` using `L0.quotKerEquivRange_symm_apply_image z h`. Simplify using `only [φ', LinearMap.comp_apply, LinearEquiv.coe_coe, this]`. Both sides reduce to the same expression. Use `⟨_, fun j => (e j).1.1, fun j => (e j).1.2, L E, LinearMap.range L0, ?_, ?_, ?_, φ', ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[LinearMap.range_eq_map]`. Conclude with `(Module.Finite.fg_top).map _`. Introduce and unpack `γ _ ⟨z, rfl⟩`. Conclude with `⟨⟨_, (hst0 γ z.1 z.2).1⟩, (key γ z.1).symm⟩`. Introduce `γ`.

Conclude with `⟨⟨y γ, Submodule.subset_span ⟨_, rfl⟩⟩, (hLE γ).symm⟩`. Introduce and unpack `γ ⟨_, z, rfl⟩`. Establish `h2` using `hφ' ⟨_, (hst0 γ z.1 z.2).1⟩ ⟨⟨_, (hst0 γ z.1 z.2).1⟩, rfl⟩`. Establish `h3` using `hφ' z ⟨z, rfl⟩`. Use `Eq.trans (Eq.trans (congrArg φ' (Subtype.ext ?_)) h2) ?_` and prove the remaining obligations.

Conclude with `key γ z.1`. Rewrite using `[(hst0 γ z.1 z.2).2, ← h3]`. Both sides reduce to the same expression. Introduce `γ`. Establish `h2` using `hφ' ⟨y γ, Submodule.subset_span ⟨_, rfl⟩⟩ ⟨⟨y γ, Submodule.subset_span ⟨_, rfl⟩⟩, rfl⟩`.

Conclude with `Eq.trans (congrArg φ' (Subtype.ext (hLE γ))) h2`.
-/
theorem factor {O K Γ X W : Type} [CommRing O] [IsNoetherianRing O] [Field K] [Algebra O K]
    (hinj : Function.Injective (algebraMap O K)) [Group Γ] [Fintype X] [AddCommGroup W] [Module O W] {n : ℕ}
    (P : X → Prop) (A : X → (Γ →* Matrix (Fin n) (Fin n) O)) (E : X → Matrix (Fin n) (Fin n) O)
    (y : Γ → X → Matrix (Fin n) (Fin n) O) (hy : ∀ γ x, y γ x = (A x γ - 1) * E x)
    (φ : (X → Matrix (Fin n) (Fin n) O) →ₗ[O] W) (ρ : Γ → W →ₗ[O] W)
    (h1 : ∀ γ δ, φ ((fun x => A x γ) * y δ) = ρ γ (φ (y δ)))
    (h0 : ∀ z ∈ Submodule.span O (Set.range y), (∀ x, P x → z x = 0) → φ z = 0) :
    ∃ (a : ℕ) (q : Fin a → X) (_ : ∀ j, P (q j)) (E' : Fin a → Fin n → K)
      (Y : Submodule O (Fin a → Fin n → K)) (_ : Y.FG)
      (hst : ∀ γ : Γ, ∀ z ∈ Y, (fun j => (mapM (algebraMap O K) (A (q j)) γ).mulVec (z j)) ∈ Y)
      (hE : ∀ γ : Γ, (fun j => (mapM (algebraMap O K) (A (q j)) γ).mulVec (E' j) - E' j) ∈ Y)
      (φ' : ↥Y →ₗ[O] W),
      (∀ (γ : Γ) (z : ↥Y), φ' ⟨_, hst γ z.1 z.2⟩ = ρ γ (φ' z)) ∧ ∀ γ, φ' ⟨_, hE γ⟩ = φ (y γ) := by
  classical
  let e := (Fintype.equivFin ({x // P x} × Fin n)).symm
  let L : (X → Matrix (Fin n) (Fin n) O) →ₗ[O] (Fin (Fintype.card ({x // P x} × Fin n)) → Fin n → K) :=
    { toFun := fun z j s => algebraMap O K (z (e j).1.1 s (e j).2)
      map_add' := fun a b => by funext j s; simp
      map_smul' := fun c a => by funext j s; simp [Algebra.smul_def] }
  have key : ∀ (γ : Γ) (z : X → Matrix (Fin n) (Fin n) O),
      (fun j => (mapM (algebraMap O K) (A (e j).1.1) γ).mulVec (L z j)) = L ((fun x => A x γ) * z) := by
    intro γ z
    funext j s
    show ∑ t, algebraMap O K (A (e j).1.1 γ s t) * algebraMap O K (z (e j).1.1 t (e j).2) =
      algebraMap O K (∑ t, A (e j).1.1 γ s t * z (e j).1.1 t (e j).2)
    simp
  let Y0 := Submodule.span O (Set.range y)
  have hmul : ∀ γ δ, (fun x => A x γ) * y δ = y (γ * δ) - y γ := by
    intro γ δ
    funext x
    simp only [Pi.mul_apply, Pi.sub_apply, hy, map_mul]
    noncomm_ring
  have hst0 : ∀ γ, ∀ z ∈ Y0, (fun x => A x γ) * z ∈ Y0 ∧ φ ((fun x => A x γ) * z) = ρ γ (φ z) := by
    intro γ z hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨δ, rfl⟩ := hz
      refine ⟨?_, h1 γ δ⟩
      rw [hmul]
      exact Y0.sub_mem (Submodule.subset_span ⟨_, rfl⟩) (Submodule.subset_span ⟨_, rfl⟩)
    | zero => simp
    | add a b _ _ ha hb =>
      rw [mul_add, map_add, map_add, map_add, ha.2, hb.2]
      exact ⟨Y0.add_mem ha.1 hb.1, rfl⟩
    | smul c a _ ha =>
      rw [mul_smul_comm, map_smul, map_smul, map_smul, ha.2]
      exact ⟨Y0.smul_mem c ha.1, rfl⟩
  have hLE : ∀ γ, (fun j => (mapM (algebraMap O K) (A (e j).1.1) γ).mulVec (L E j) - L E j) = L (y γ) := by
    intro γ
    have : y γ = (fun x => A x γ) * E - E := by
      funext x
      simp [hy, sub_mul]
    rw [this, map_sub, ← key]
    rfl
  let L0 := L.domRestrict Y0
  have hker : LinearMap.ker L0 ≤ LinearMap.ker (φ.domRestrict Y0) := by
    intro z hz
    refine h0 z.1 z.2 fun x hx => ?_
    ext s t
    apply hinj
    have := congrFun (congrFun (LinearMap.mem_ker.mp hz) (e.symm (⟨x, hx⟩, t))) s
    simpa [L0, L] using this
  let φ' : ↥(LinearMap.range L0) →ₗ[O] W :=
    ((LinearMap.ker L0).liftQ (φ.domRestrict Y0) hker) ∘ₗ (L0.quotKerEquivRange.symm : _ →ₗ[O] _)
  have hφ' : ∀ (z : Y0) (h : L z.1 ∈ LinearMap.range L0), φ' ⟨L z.1, h⟩ = φ z.1 := by
    intro z h
    have : L0.quotKerEquivRange.symm ⟨L z.1, h⟩ = (LinearMap.ker L0).mkQ z :=
      L0.quotKerEquivRange_symm_apply_image z h
    simp only [φ', LinearMap.comp_apply, LinearEquiv.coe_coe, this]
    rfl
  refine ⟨_, fun j => (e j).1.1, fun j => (e j).1.2, L E, LinearMap.range L0, ?_, ?_, ?_, φ', ?_, ?_⟩
  · rw [LinearMap.range_eq_map]
    exact (Module.Finite.fg_top).map _
  · rintro γ _ ⟨z, rfl⟩
    exact ⟨⟨_, (hst0 γ z.1 z.2).1⟩, (key γ z.1).symm⟩
  · intro γ
    exact ⟨⟨y γ, Submodule.subset_span ⟨_, rfl⟩⟩, (hLE γ).symm⟩
  · rintro γ ⟨_, z, rfl⟩
    have h2 := hφ' ⟨_, (hst0 γ z.1 z.2).1⟩ ⟨⟨_, (hst0 γ z.1 z.2).1⟩, rfl⟩
    have h3 := hφ' z ⟨z, rfl⟩
    refine Eq.trans (Eq.trans (congrArg φ' (Subtype.ext ?_)) h2) ?_
    · exact key γ z.1
    rw [(hst0 γ z.1 z.2).2, ← h3]
    rfl
  · intro γ
    have h2 := hφ' ⟨y γ, Submodule.subset_span ⟨_, rfl⟩⟩ ⟨⟨y γ, Submodule.subset_span ⟨_, rfl⟩⟩, rfl⟩
    exact Eq.trans (congrArg φ' (Subtype.ext (hLE γ))) h2

variable {D : D7} (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (S : IdempotentChoiceData D.nd i)

/- English proof (translation)
Use `⟨1, fun _ => algebraMap (D.nd.O i) _ (((chiU D.nd i 1 γ)⁻¹ : (D.nd.O i)ˣ) : D.nd.O i), fun _ => γ, fun _ => S.T'.algebraMap_mem _, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `x'`. Simplify using `[rTwO, twistM]`.
-/
theorem inR'_tw (γ : GE D.nd) : InR' D.nd r S fun x' => rTwO D.nd i r (S.p x') γ := by
  refine ⟨1, fun _ => algebraMap (D.nd.O i) _ (((chiU D.nd i 1 γ)⁻¹ : (D.nd.O i)ˣ) : D.nd.O i), fun _ => γ,
    fun _ => S.T'.algebraMap_mem _, ?_⟩
  funext x'
  simp [rTwO, twistM]

/- English proof (translation)
Use `⟨1, fun _ => 1, fun _ => 1, fun _ => one_mem _, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `x'`. Simplify using the standard rewrite rules.
-/
theorem inR'_one : InR' D.nd r S 1 := by
  refine ⟨1, fun _ => 1, fun _ => 1, fun _ => one_mem _, ?_⟩
  funext x'
  simp

/- English proof (translation)
Assemble the required witnesses or components as `⟨1, fun _ => 1, fun _ => γ, fun _ => inR'_one i r S, by simp⟩`.
-/
theorem inY_yg (γ : GE D.nd) : InY D.nd r S (yg D.nd r S γ) :=
  ⟨1, fun _ => 1, fun _ => γ, fun _ => inR'_one i r S, by simp⟩

/- English proof (translation)
Proceed by induction on `hz using Submodule.span_induction with`. Consider the case `mem z hz`. Take `⟨δ, rfl⟩` from `hz`. Conclude with `inY_yg i r S δ`. Consider the case `zero => exact ⟨0, Fin.elim0, Fin.elim0, fun k => k.elim0, by simp⟩`.

Consider the case `add a b _ _ ha hb`. Take `⟨m, a, γ, ha, rfl⟩` from `ha`. Take `⟨m', a', γ', ha', rfl⟩` from `hb`. Use `⟨m + m', Fin.append a a', Fin.append γ γ', fun k => ?_, ?_⟩` and prove the remaining obligations. Use `Fin.addCases (fun k => ?_) (fun k => ?_) k` and prove the remaining obligations.

Simplify using `using ha k`. Simplify using `using ha' k`. Rewrite using `[Fin.sum_univ_add]`. Simplify using the standard rewrite rules. Consider the case `smul c a _ ha`.

Take `⟨m, a, γ, ha, rfl⟩` from `ha`. Use `⟨m, fun k => c • a k, γ, fun k => ?_, ?_⟩` and prove the remaining obligations. Take `⟨m', f, g, hf, h⟩` from `ha k`. Use `⟨m', fun j => c • f j, g, fun j => S.T'.smul_mem (hf j) c, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `x'`.

Simplify using `[h, Finset.smul_sum, mul_smul]`. Simplify using `[Finset.smul_sum]`.
-/
theorem inY_of_span (z : S.X' → MatN D.nd i)
    (hz : z ∈ Submodule.span (D.nd.O i) (Set.range (yg D.nd r S))) : InY D.nd r S z := by
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨δ, rfl⟩ := hz
    exact inY_yg i r S δ
  | zero => exact ⟨0, Fin.elim0, Fin.elim0, fun k => k.elim0, by simp⟩
  | add a b _ _ ha hb =>
    obtain ⟨m, a, γ, ha, rfl⟩ := ha
    obtain ⟨m', a', γ', ha', rfl⟩ := hb
    refine ⟨m + m', Fin.append a a', Fin.append γ γ', fun k => ?_, ?_⟩
    · refine Fin.addCases (fun k => ?_) (fun k => ?_) k
      · simpa using ha k
      · simpa using ha' k
    · rw [Fin.sum_univ_add]
      simp
  | smul c a _ ha =>
    obtain ⟨m, a, γ, ha, rfl⟩ := ha
    refine ⟨m, fun k => c • a k, γ, fun k => ?_, ?_⟩
    · obtain ⟨m', f, g, hf, h⟩ := ha k
      refine ⟨m', fun j => c • f j, g, fun j => S.T'.smul_mem (hf j) c, ?_⟩
      funext x'
      simp [h, Finset.smul_sum, mul_smul]
    · simp [Finset.smul_sum]

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 2000000 in

/- English proof (translation)
Unfold `cocW at hf`. Proceed by induction on `hf using Submodule.span_induction with`. Consider the case `mem f hf`. Take `⟨φ, h1, h0, rfl⟩` from `hf`. Take `⟨a, q, hq, E', Y, hY, hst, hE, φ', h2, h3⟩` from `factor (K := KK D.nd i) (IsFractionRing.injective _ _) (fun x' => S.p x' ∈ Xs) (fun x' => rTwO D.nd i r (S.p x')) (Eel D.nd S) (yg D.nd r S) (fun γ x' => by simp [yg, rTwO, twistM, sub_mul]) φ (fun γ => WKG M γ) (fun γ δ => by`.

Rewrite using `[h1 _ (inR'_tw i r S γ) _ (inY_yg i r S δ), hψ]`. Take `⟨u, hu⟩` from `Submodule.Quotient.mk_surjective _ (φ (yg D.nd r S δ))`. Rewrite using `[← hu]`. Use the proof step `rfl)`. Use the proof step `(fun z hz => h0 z (inY_of_span i r S z hz))`.

Apply `Submodule.subset_span` to reduce the goal to its premises. Use `⟨a, fun j => S.p (q j), hq, E', Y, hY, hst, hE, φ', h2, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `g`. Conclude with `congrArg (Br.phi (D.nbr i w hw) k) (h3 _).symm`. Consider the case `zero`.

Establish `e : locFun i M w hw 0 = 0`. Use function extensionality and compare the values at `g`. Conclude with `(Br.phi (D.nbr i w hw) k).map_zero`. Unfold `InCut`. Rewrite using `[e]`.

Conclude with `Submodule.zero_mem _`. Consider the case `add f f' _ _ h h'`. Establish `e : locFun i M w hw (f + f') = locFun i M w hw f + locFun i M w hw f'`. Use function extensionality and compare the values at `g`. Conclude with `(Br.phi (D.nbr i w hw) k).map_add _ _`.

Unfold `InCut at *`. Rewrite using `[e]`. Conclude with `Submodule.add_mem _ h h'`. Consider the case `smul c f _ h`. Establish `e : locFun i M w hw (c • f) = ((D.nbr i w hw).eO c : Br.OLL D.nbr i w hw) • locFun i M w hw f`.

Use function extensionality and compare the values at `g`. Conclude with `(Br.phi (D.nbr i w hw) k).map_smulₛₗ c _`. Unfold `InCut at *`. Rewrite using `[e]`. Conclude with `Submodule.smul_mem _ _ h`.
-/
theorem inCut_of_cocW (Xs : Set (D.nd.X i)) {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i))
    (ψ : (S.X' → MatN D.nd i) → Matrix (Fin k) (Fin k) (D.nd.O i))
    (hψ : ∀ γ, ψ (fun x' => rTwO D.nd i r (S.p x') γ) = M γ)
    (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (f : GE D.nd → KOG (D.nd.O i) k) (hf : f ∈ cocW i r S Xs ψ) : InCut i r Xs M w hw f := by
  unfold cocW at hf
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨φ, h1, h0, rfl⟩ := hf
    obtain ⟨a, q, hq, E', Y, hY, hst, hE, φ', h2, h3⟩ :=
      factor (K := KK D.nd i) (IsFractionRing.injective _ _) (fun x' => S.p x' ∈ Xs)
        (fun x' => rTwO D.nd i r (S.p x')) (Eel D.nd S) (yg D.nd r S)
        (fun γ x' => by simp [yg, rTwO, twistM, sub_mul]) φ (fun γ => WKG M γ)
        (fun γ δ => by
          rw [h1 _ (inR'_tw i r S γ) _ (inY_yg i r S δ), hψ]
          obtain ⟨u, hu⟩ := Submodule.Quotient.mk_surjective _ (φ (yg D.nd r S δ))
          rw [← hu]
          rfl)
        (fun z hz => h0 z (inY_of_span i r S z hz))
    apply Submodule.subset_span
    refine ⟨a, fun j => S.p (q j), hq, E', Y, hY, hst, hE, φ', h2, ?_⟩
    funext g
    exact congrArg (Br.phi (D.nbr i w hw) k) (h3 _).symm
  | zero =>
    have e : locFun i M w hw 0 = 0 := by
      funext g
      exact (Br.phi (D.nbr i w hw) k).map_zero
    unfold InCut
    rw [e]
    exact Submodule.zero_mem _
  | add f f' _ _ h h' =>
    have e : locFun i M w hw (f + f') = locFun i M w hw f + locFun i M w hw f' := by
      funext g
      exact (Br.phi (D.nbr i w hw) k).map_add _ _
    unfold InCut at *
    rw [e]
    exact Submodule.add_mem _ h h'
  | smul c f _ h =>
    have e : locFun i M w hw (c • f) =
        ((D.nbr i w hw).eO c : Br.OLL D.nbr i w hw) • locFun i M w hw f := by
      funext g
      exact (Br.phi (D.nbr i w hw) k).map_smulₛₗ c _
    unfold InCut at *
    rw [e]
    exact Submodule.smul_mem _ _ h

/- English proof (translation)
Introduce `D i r ρ π Xs S _ hG _ w hw`. Take `⟨-, hdec, hψ, -, -, -, -, -, -, ⟨hπ, -⟩, -⟩` from `hG`. Establish `key : ∀ γ u, (((S.ψρ fun x' => rTwO D.nd i r (S.p x') γ).map (toK D.nd i)).mulVec (S.e u).1, fun c : Fin D.R.t => toK D.nd i (S.ψχ c fun x' => rTwO D.nd i r (S.p x') γ) * (S.e u).2 c) = toK D.nd i (((chiU D.nd i 1 γ)⁻¹ : (D.nd.O i)ˣ) : D.nd.O i) • ((mapM (toK D.nd i) (rhoO D.nd i …`. Introduce `γ u`. Rewrite using `[← hψ _ (inR'_tw i r S γ) u, ← hdec, ← map_smul, hπ, ← Matrix.smul_mulVec]`.

Use `congr 2`. Use extensionality with `p q`. Simplify using `[mapM, rTwO, twistM]`. Use `⟨fun f hf => inCut_of_cocW i r S Xs _ _ (fun γ => ?_) w hw f hf, fun c f hf => inCut_of_cocW i r S Xs _ _ (fun γ => ?_) w hw f hf⟩` and prove the remaining obligations. Use extensionality with `p q`.

Apply `IsFractionRing.injective (D.nd.O i) (KK D.nd i)` to reduce the goal to its premises. Establish `h` using `congrArg (fun z => z.1 p) (key γ (S.e.symm (Pi.single q 1, 0)))`. Simplify `h` using `[mapM, WpO, twistM]`. Use extensionality with `p q`. Apply `IsFractionRing.injective (D.nd.O i) (KK D.nd i)` to reduce the goal to its premises.

Establish `h` using `congrArg (fun z => z.2 c) (key γ (S.e.symm (0, Pi.single c 1)))`. Take `rfl : p = q` from `Subsingleton.elim _ _`. Simplify `h` using `[chiRatO, twistM, mul_comm]`.
-/
theorem main : ∀ (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (Xs : Set (D.nd.X i)) (S : IdempotentChoiceData D.nd i), GoodR D.nd i r → GoodCongruenceObjects D.nd r ρ π S → π ∈ Xs → ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)), (∀ f ∈ cocRho i r S Xs, InCut i r Xs (WpO D.nd i ρ π) w hw f) ∧ ∀ c : Fin D.R.t, ∀ f ∈ cocChi i r S Xs c, InCut i r Xs (chiRatO D.nd i ((c : ℕ) + 1)) w hw f := by
  intro D i r ρ π Xs S _ hG _ w hw
  obtain ⟨-, hdec, hψ, -, -, -, -, -, -, ⟨hπ, -⟩, -⟩ := hG
  have key : ∀ γ u, (((S.ψρ fun x' => rTwO D.nd i r (S.p x') γ).map (toK D.nd i)).mulVec (S.e u).1,
      fun c : Fin D.R.t => toK D.nd i (S.ψχ c fun x' => rTwO D.nd i r (S.p x') γ) * (S.e u).2 c) =
      toK D.nd i (((chiU D.nd i 1 γ)⁻¹ : (D.nd.O i)ˣ) : D.nd.O i) •
        ((mapM (toK D.nd i) (rhoO D.nd i ρ π) γ).mulVec (S.e u).1,
        fun c : Fin D.R.t => toK D.nd i ((chiU D.nd i ((c : ℕ) + 1) γ : (D.nd.O i)ˣ) : D.nd.O i) * (S.e u).2 c) := by
    intro γ u
    rw [← hψ _ (inR'_tw i r S γ) u, ← hdec, ← map_smul, hπ, ← Matrix.smul_mulVec]
    congr 2
    ext p q
    simp [mapM, rTwO, twistM]
  refine ⟨fun f hf => inCut_of_cocW i r S Xs _ _ (fun γ => ?_) w hw f hf,
    fun c f hf => inCut_of_cocW i r S Xs _ _ (fun γ => ?_) w hw f hf⟩
  · ext p q
    apply IsFractionRing.injective (D.nd.O i) (KK D.nd i)
    have h := congrArg (fun z => z.1 p) (key γ (S.e.symm (Pi.single q 1, 0)))
    simpa [mapM, WpO, twistM] using h
  · ext p q
    apply IsFractionRing.injective (D.nd.O i) (KK D.nd i)
    have h := congrArg (fun z => z.2 c) (key γ (S.e.symm (0, Pi.single c 1)))
    obtain rfl : p = q := Subsingleton.elim _ _
    simpa [chiRatO, twistM, mul_comm] using h

end GlobalTheory.Cut.LocCoc
