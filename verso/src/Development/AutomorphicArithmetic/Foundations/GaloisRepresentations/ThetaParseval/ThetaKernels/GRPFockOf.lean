import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.BlockDeterminants.ExponentialEntries.Frames
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.BlockDeterminants.ExponentialEntries.ExpFirst
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.BlockDeterminants.ExponentialEntries.ExpSecond
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.BlockDeterminants.ExponentialEntries.ExpSum
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.BlockDeterminants.ExponentialEntries.TprodNe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JmConjTranspose
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.IsLatRepL
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.GalTPDefs
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ThetaBasicK

set_option synthInstance.maxHeartbeats 200000

section
open scoped TensorProduct Matrix Classical
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.RealLift UpperTheory.TP.RP
noncomputable section
namespace UpperTheory.TP.RP.FockModelActions
/- English proof (translation)
Establish `hE : ∀ l l' : Ln n 0 d 0, omE l l' (1 : Formalism.BasicNotions.TH.Pol n 0 d 0) = if l = l' then (1 / 2 : ℂ) • (1 : Formalism.BasicNotions.TH.Pol n 0 d 0) else 0`. Introduce and unpack `l ⟨(i | i), (j | j)⟩`. Establish `h0 : lowB ((Sum.inl i, Sum.inl j) : Ln n 0 d 0) (1 : Formalism.BasicNotions.TH.Pol n 0 d 0) = 0`. Simplify using `[lowB, linePos]`. Simplify using `only [omE, LinearMap.add_apply, Module.End.mul_apply, h0, map_zero, zero_add]`.

Apply the tactic sequence `split_ifs <;> simp`. Conclude with `j.elim0`. Conclude with `i.elim0`. Conclude with `i.elim0`. Simplify using `only [omAct, LinearMap.sum_apply, LinearMap.smulRight_apply, Matrix.entryLinearMap_apply, LinearMap.smul_apply, hE]`.

Simplify using `only [smul_ite, smul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true, Matrix.trace, Matrix.diag_apply]`. Rewrite using `[← Finset.sum_smul, smul_smul, mul_comm]`.
-/
private theorem omAct_one_pk {n d : ℕ} (M : Matrix (Ln n 0 d 0) (Ln n 0 d 0) ℂ) :
    omAct n 0 d 0 M (1 : Formalism.BasicNotions.TH.Pol n 0 d 0) = ((1 / 2 : ℂ) * M.trace) • (1 : Formalism.BasicNotions.TH.Pol n 0 d 0) := by
  have hE : ∀ l l' : Ln n 0 d 0, omE l l' (1 : Formalism.BasicNotions.TH.Pol n 0 d 0) =
      if l = l' then (1 / 2 : ℂ) • (1 : Formalism.BasicNotions.TH.Pol n 0 d 0) else 0 := by
    rintro l ⟨(i | i), (j | j)⟩
    · have h0 : lowB ((Sum.inl i, Sum.inl j) : Ln n 0 d 0) (1 : Formalism.BasicNotions.TH.Pol n 0 d 0) = 0 := by
        simp [lowB, linePos]
      simp only [omE, LinearMap.add_apply, Module.End.mul_apply, h0, map_zero, zero_add]
      split_ifs <;> simp
    · exact j.elim0
    · exact i.elim0
    · exact i.elim0
  simp only [omAct, LinearMap.sum_apply, LinearMap.smulRight_apply, Matrix.entryLinearMap_apply, LinearMap.smul_apply, hE]
  simp only [smul_ite, smul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true, Matrix.trace, Matrix.diag_apply]
  rw [← Finset.sum_smul, smul_smul, mul_comm]
/- English proof (translation)
Establish `: (Matrix.kroneckerMapBilinear (LinearMap.mul ℂ ℂ)).flip (1 : Mat d 0) Y = Matrix.kroneckerMap (· * ·) Y (1 : Mat d 0)` using `rfl`. Rewrite using `[fockAct1, LinearMap.comp_apply, this, omAct_one_pk]`. Use `congr 1`. Rewrite using `[Matrix.trace_kronecker Y (1 : Mat d 0), Matrix.trace_one]`. Simplify using `only [Fintype.card_sum, Fintype.card_fin, add_zero]`.

Expand and normalize the polynomial expressions, which then agree.
-/
private theorem fock_first_action_one_polynomial {n d : ℕ} (Y : Mat n 0) :
    fockAct1 n 0 d 0 Y (1 : Formalism.BasicNotions.TH.Pol n 0 d 0) = (((d : ℂ) / 2) * Y.trace) • (1 : Formalism.BasicNotions.TH.Pol n 0 d 0) := by
  have : (Matrix.kroneckerMapBilinear (LinearMap.mul ℂ ℂ)).flip (1 : Mat d 0) Y = Matrix.kroneckerMap (· * ·) Y (1 : Mat d 0) := rfl
  rw [fockAct1, LinearMap.comp_apply, this, omAct_one_pk]
  congr 1
  rw [Matrix.trace_kronecker Y (1 : Mat d 0), Matrix.trace_one]
  simp only [Fintype.card_sum, Fintype.card_fin, add_zero]
  ring
/- English proof (translation)
Establish `: (Matrix.kroneckerMapBilinear (LinearMap.mul ℂ ℂ)) (1 : Mat n 0) Y = Matrix.kroneckerMap (· * ·) (1 : Mat n 0) Y` using `rfl`. Rewrite using `[fockAct2, LinearMap.comp_apply, this, omAct_one_pk]`. Use `congr 1`. Rewrite using `[Matrix.trace_kronecker (1 : Mat n 0) Y, Matrix.trace_one]`. Simplify using `only [Fintype.card_sum, Fintype.card_fin, add_zero]`.

Expand and normalize the polynomial expressions, which then agree.
-/
private theorem fock_second_action_one_polynomial {n d : ℕ} (Y : Mat d 0) :
    fockAct2 n 0 d 0 Y (1 : Formalism.BasicNotions.TH.Pol n 0 d 0) = (((n : ℂ) / 2) * Y.trace) • (1 : Formalism.BasicNotions.TH.Pol n 0 d 0) := by
  have : (Matrix.kroneckerMapBilinear (LinearMap.mul ℂ ℂ)) (1 : Mat n 0) Y = Matrix.kroneckerMap (· * ·) (1 : Mat n 0) Y := rfl
  rw [fockAct2, LinearMap.comp_apply, this, omAct_one_pk]
  congr 1
  rw [Matrix.trace_kronecker (1 : Mat n 0) Y, Matrix.trace_one]
  simp only [Fintype.card_sum, Fintype.card_fin, add_zero]
  ring
/- English proof (translation)
Use extensionality with `a b`. Break down `a with a | a` into its components or cases. Break down `b with b | b` into its components or cases. Simplify using `[Jm, Formalism.UG.Jpq, Matrix.one_apply]`. Conclude with `b.elim0`.

Conclude with `a.elim0`.
-/
private theorem jm_zero_pk (N : ℕ) : Jm N 0 = 1 := by
  ext a b
  rcases a with a | a
  · rcases b with b | b
    · simp [Jm, Formalism.UG.Jpq, Matrix.one_apply]
    · exact b.elim0
  · exact a.elim0
/- English proof (translation)
Introduce and unpack `(a | a) (b | b) h`. Conclude with `absurd trivial h`. Conclude with `b.elim0`. Conclude with `a.elim0`. Conclude with `a.elim0`.
-/
private theorem isKC_all_pk {N : ℕ} (Y : Mat N 0) : IsKC Y := by
  rintro (a | a) (b | b) h
  · exact absurd trivial h
  · exact b.elim0
  · exact a.elim0
  · exact a.elim0
/- English proof (translation)
The claim follows from `LinearMap.ext fun v => sub_eq_zero.1 ((Module.forall_dual_apply_eq_zero_iff ℂ _).1 fun l => by rw [map_sub, (h v l).unique (h' v l), sub_self])`.
-/
private theorem isExp_unique_pk {V : Type} [AddCommGroup V] [Module ℂ V] {L U U' : Module.End ℂ V} (h : IsExp L U) (h' : IsExp L U') :
    U = U' :=
  LinearMap.ext fun v => sub_eq_zero.1 ((Module.forall_dual_apply_eq_zero_iff ℂ _).1 fun l => by
    rw [map_sub, (h v l).unique (h' v l), sub_self])
/- English proof (translation)
Rewrite using `[sumPl, LinearMap.sum_apply, Finset.sum_smul]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[atPl, PiTensorProduct.map_tprod]`. Establish `e : (fun j => Function.update (fun j => (LinearMap.id : V j →ₗ[ℂ] V j)) i (L i) j (f j)) = Function.update f i (c i • f i)`. Use function extensionality and compare the values at `j`.

Distinguish the cases in `hj : j = i`. Substitute `hj` using the available equality. Simplify using `[h]`. Simplify using `[Function.update_of_ne hj]`. Rewrite using `[e, MultilinearMap.map_update_smul, Function.update_eq_self]`.
-/
private theorem sumPl_tprod_pk {ι : Type} [Fintype ι] [DecidableEq ι] {V : ι → Type} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
    (L : ∀ i, Module.End ℂ (V i)) (f : ∀ i, V i) (c : ι → ℂ) (h : ∀ i, L i (f i) = c i • f i) :
    sumPl L (PiTensorProduct.tprod ℂ f) = (∑ i, c i) • PiTensorProduct.tprod ℂ f := by
  rw [sumPl, LinearMap.sum_apply, Finset.sum_smul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [atPl, PiTensorProduct.map_tprod]
  have e : (fun j => Function.update (fun j => (LinearMap.id : V j →ₗ[ℂ] V j)) i (L i) j (f j)) = Function.update f i (c i • f i) := by
    funext j
    by_cases hj : j = i
    · subst hj; simp [h]
    · simp [Function.update_of_ne hj]
  rw [e, MultilinearMap.map_update_smul, Function.update_eq_self]
section Gen
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n d P Q R S r s : ℕ} {β : Type} [Fintype β] [DecidableEq β]
/- English proof (translation)
Take `⟨U, hU, hSA⟩` from `Main.i_expact F (Fin n × Fin d) _ Φ _ (om'.comp γ) (Main.i_locfin _ _ _ fun w => hloc _ _) (fun t l hl => hadm _ l hl) (fun T => hact γ hγ Y hY T)`. Conclude with `⟨U, hU, fun T => (Main.i_actslaws F _ (Φ T) (Φ (U T)) (Φ T)).2.1 _ (map_zero _) (hSA T)⟩`.
-/
private theorem exp_gen_pk {τ : ∀ w : InfinitePlace F, EmbOver E w} {J : Matrix β β (AE F E)}
    {C : InfinitePlace F → Matrix β (Ix r s) ℂ} {om' : UG (cA σ) J →* Module.End ℂ ((Fin n × Fin d → AF F) → ℂ)}
    {Φ : Tens F P Q R S →ₗ[ℂ] SInf F (Fin n × Fin d)} {act : Mat r s →ₗ[ℂ] Module.End ℂ (Formalism.BasicNotions.TH.Pol P Q R S)}
    {c : InfinitePlace F → ℂ} (hact : ActsBy τ C om' Φ act c)
    (hadm : ∀ g, ∀ l ∈ (adeleClass F).adm (Fin n × Fin d), l ∘ₗ om' g ∈ (adeleClass F).adm (Fin n × Fin d))
    (hloc : ∀ (Y : Mat r s) (z : ℂ), LocFin (act Y + z • 1))
    {γ : Multiplicative ℝ →* UG (cA σ) J} (hγ : γ ∈ RLines σ J) {Y : InfinitePlace F → Mat r s} (hY : IsGen τ C γ Y) :
    ∃ U : Module.End ℂ (Tens F P Q R S), IsExp (sumPl fun w => act (Y w) + (c w * (Y w).trace) • 1) U ∧
      ∀ T, Acts (evI F) (om' (γ (Multiplicative.ofAdd 1))) (Φ T) (Φ (U T)) := by
  obtain ⟨U, hU, hSA⟩ := Main.i_expact F (Fin n × Fin d) _ Φ _ (om'.comp γ) (Main.i_locfin _ _ _ fun w => hloc _ _)
    (fun t l hl => hadm _ l hl) (fun T => hact γ hγ Y hY T)
  exact ⟨U, hU, fun T => (Main.i_actslaws F _ (Φ T) (Φ (U T)) (Φ T)).2.1 _ (map_zero _) (hSA T)⟩
/- English proof (translation)
Apply `Subtype.ext` to reduce the goal to its premises. Apply `Units.ext` to reduce the goal to its premises. Use `show mat k = 1`. Use extensionality with `i j`. Rewrite using `[← sub_eq_zero]`.

Use `GlobalTheory.RealLift.KLineProof.eq_zero_of_piInf hcm B.emb _ (fun u hu => ?_) fun w => ?_` and prove the remaining obligations. Establish `a` using `congrFun (congrFun (hk u hu) i) j`. Simplify `a` using `only [Matrix.smul_apply, Matrix.sub_apply, Matrix.zero_apply]`. Take `⟨A', hA'⟩` from `(hC w).2`. Establish `e` using `congrArg (· * A') (h w)`.

Simplify using `only [Matrix.mul_assoc, hA', Matrix.mul_one] at e`. Use `congrFun (congrFun e i) j` as an intermediate fact. Simplify using `only [Matrix.map_apply] at this`. Rewrite using `[map_sub, this, sub_eq_zero, Matrix.one_apply, Matrix.one_apply]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
private theorem eq_one_of_frame_pk {B : Base F E} {N : ℕ} {W : Spc F E N} (hcm : IsCMExt F E σ) {b : ℂ}
    {C : InfinitePlace F → Matrix (Fin N) (Ix r s) ℂ} (hC : ∀ w, IsFrame (b • (incM F W.J).map (piInf (B.emb w))) (C w))
    {k : UA σ W.J} (hk : k ∈ UAt σ W (evI F)) (h : ∀ w, (mat k).map (piInf (B.emb w)) * C w = C w) : k = 1 := by
  apply Subtype.ext; apply Units.ext
  show mat k = 1
  ext i j
  rw [← sub_eq_zero]
  refine GlobalTheory.RealLift.KLineProof.eq_zero_of_piInf hcm B.emb _ (fun u hu => ?_) fun w => ?_
  · have a := congrFun (congrFun (hk u hu) i) j
    simpa only [Matrix.smul_apply, Matrix.sub_apply, Matrix.zero_apply] using a
  · obtain ⟨A', hA'⟩ := (hC w).2
    have e := congrArg (· * A') (h w)
    simp only [Matrix.mul_assoc, hA', Matrix.mul_one] at e
    have := congrFun (congrFun e i) j
    simp only [Matrix.map_apply] at this
    rw [map_sub, this, sub_eq_zero, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
/- English proof (translation)
Proceed by induction on `hk using Subgroup.closure_induction with`. Consider the case `mem x hx => exact hx`. Consider the case `one => intro u _`. Simplify using `[mat]`. Consider the case `mul x y _ _ hx hy`.

Introduce `u hu`. Establish `e : mat (x * y) - 1 = (mat x - 1) * mat y + (mat y - 1)` using `by show mat x * mat y - 1 = _ noncomm_ring`. Rewrite using `[e, smul_add, ← Matrix.smul_mul, hx u hu, hy u hu, Matrix.zero_mul, add_zero]`. Consider the case `inv x _ hx`. Introduce `u hu`.

Establish `e : mat x⁻¹ - 1 = - (mat x⁻¹ * (mat x - 1))`. Establish `h1 : mat x⁻¹ * mat x = 1` using `by show mat (x⁻¹ * x) = 1`. Simplify using `[mat]`. Rewrite using `[mul_sub, h1, mul_one]`. Normalize the expressions using the abelian group laws.

Rewrite using `[e, smul_neg, ← Matrix.mul_smul, hx u hu, Matrix.mul_zero, neg_zero]`.
-/
private theorem mem_uat_of_closure_pk {N : ℕ} {W : Spc F E N} {k : UA σ W.J} (hk : k ∈ Subgroup.closure (UAt σ W (evI F))) :
    k ∈ UAt σ W (evI F) := by
  induction hk using Subgroup.closure_induction with
  | mem x hx => exact hx
  | one => intro u _; simp [mat]
  | mul x y _ _ hx hy =>
    intro u hu
    have e : mat (x * y) - 1 = (mat x - 1) * mat y + (mat y - 1) := by
      show mat x * mat y - 1 = _
      noncomm_ring
    rw [e, smul_add, ← Matrix.smul_mul, hx u hu, hy u hu, Matrix.zero_mul, add_zero]
  | inv x _ hx =>
    intro u hu
    have e : mat x⁻¹ - 1 = - (mat x⁻¹ * (mat x - 1)) := by
      have h1 : mat x⁻¹ * mat x = 1 := by
        show mat (x⁻¹ * x) = 1
        simp [mat]
      rw [mul_sub, h1, mul_one]; abel
    rw [e, smul_neg, ← Matrix.mul_smul, hx u hu, Matrix.mul_zero, neg_zero]
end Gen
section CM
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n d P Q R S : ℕ}
/- English proof (translation)
Introduce `k hk T`. Establish `hat : e k ∈ UAt (UpperTheory.TP.cj E) W (evI (maximalRealSubfield E))` using `mem_uat_of_closure_pk ((he.inf k).2 hk)`. Establish `hθ1 : ∀ w, W.θ w = 1` using `fun w => by`. Take `⟨A', hA'⟩` from `(hC w).2`. Use `congrArg (· * A') (hθ w)` as an intermediate fact.

Simplify `this` using `only [jm_zero_pk, Matrix.mul_one, Matrix.mul_assoc, hA']`. Take `⟨γ, hγ, Y, hgen, -, hγ1⟩` from `Main.i_kline Main.i_lineex (maximalRealSubfield E) E (UpperTheory.TP.cj E) (Fin N) N 0 B.emb (incM _ W.J) b C W.θ hcm hC hθ (e k) hat fun w => by rw [hθ1 w]; exact Commute.one_right _`. Establish `hg : ∀ w, ∀ a b, (GlobalTheory.UnitaryBC.cEmb (B.emb w).1 k).1 a b = NormedSpace.exp (Y w) (Sum.inl a) (Sum.inl b)` using `fun w => by`. Use `hlast w _ _ ?_` and prove the remaining obligations. Establish `h1` using `hgen 1 w`.

Rewrite `h1` using `[one_smul, hγ1]`. Rewrite using `[← he.emb w (B.emb w) k]`. Conclude with `h1`. Take `⟨U, hU1, hU2⟩` from `exp_gen_pk hact hadm hloc hγ hgen`. Establish `e2` using `isExp_unique_pk hU1 (UpperTheory.TP.RP.expSum _ _ (fun w => hloc _ _) fun w => hU w (Y w) _ (hg w))`.

Use `hU2 T` as an intermediate fact. Rewrite `this` using `[hγ1, e2]`. Then use the resulting hypothesis.
-/
private theorem acts_of_k_pk (hcm : IsCMExt (maximalRealSubfield E) E (UpperTheory.TP.cj E)) {B : Base (maximalRealSubfield E) E} {N : ℕ}
    {W : Spc (maximalRealSubfield E) E N} {e : GlobalTheory.UnitaryBC.UA E N ≃ₜ* UA (UpperTheory.TP.cj E) W.J} (he : UpperTheory.TP.IsBr W e) {b : ℂ}
    {C : InfinitePlace (maximalRealSubfield E) → Matrix (Fin N) (Ix N 0) ℂ}
    (hC : ∀ w, IsFrame (b • (incM (maximalRealSubfield E) W.J).map (piInf (B.emb w))) (C w))
    (hθ : ∀ w, W.θ w * C w = C w * Jm N 0)
    (hlast : ∀ w (g : Matrix (Fin N) (Fin N) ℂ) (Y : Mat N 0), g * C w = C w * NormedSpace.exp Y →
      ∀ a b, g a b = NormedSpace.exp Y (Sum.inl a) (Sum.inl b))
    {Φ : Tens (maximalRealSubfield E) P Q R S →ₗ[ℂ] SInf (maximalRealSubfield E) (Fin n × Fin d)}
    {om' : UA (UpperTheory.TP.cj E) W.J →* Module.End ℂ ((Fin n × Fin d → AF (maximalRealSubfield E)) → ℂ)}
    {act : Mat N 0 →ₗ[ℂ] Module.End ℂ (Formalism.BasicNotions.TH.Pol P Q R S)} {c : InfinitePlace (maximalRealSubfield E) → ℂ}
    (hact : ActsBy B.emb C om' Φ act c)
    (hadm : ∀ g, ∀ l ∈ (adeleClass (maximalRealSubfield E)).adm (Fin n × Fin d),
      l ∘ₗ om' g ∈ (adeleClass (maximalRealSubfield E)).adm (Fin n × Fin d))
    (hloc : ∀ (Y : Mat N 0) (z : ℂ), LocFin (act Y + z • 1))
    (Ug : InfinitePlace (maximalRealSubfield E) → GL (Fin N) ℂ → Module.End ℂ (Formalism.BasicNotions.TH.Pol P Q R S))
    (hU : ∀ w (Y : Mat N 0) (g : GL (Fin N) ℂ), (∀ a b, g.1 a b = NormedSpace.exp Y (Sum.inl a) (Sum.inl b)) →
      IsExp (act Y + (c w * Y.trace) • 1) (Ug w g)) :
    ∀ k ∈ GlobalTheory.UnitaryBC.infU E N, ∀ T, Acts (evI (maximalRealSubfield E)) (om' (e k)) (Φ T)
      (Φ (PiTensorProduct.map (fun w => Ug w (GlobalTheory.UnitaryBC.cEmb (B.emb w).1 k)) T)) := by
  intro k hk T
  have hat : e k ∈ UAt (UpperTheory.TP.cj E) W (evI (maximalRealSubfield E)) := mem_uat_of_closure_pk ((he.inf k).2 hk)
  have hθ1 : ∀ w, W.θ w = 1 := fun w => by
    obtain ⟨A', hA'⟩ := (hC w).2
    have := congrArg (· * A') (hθ w)
    simpa only [jm_zero_pk, Matrix.mul_one, Matrix.mul_assoc, hA'] using this
  obtain ⟨γ, hγ, Y, hgen, -, hγ1⟩ := Main.i_kline Main.i_lineex (maximalRealSubfield E) E (UpperTheory.TP.cj E) (Fin N) N 0 B.emb
    (incM _ W.J) b C W.θ hcm hC hθ (e k) hat fun w => by rw [hθ1 w]; exact Commute.one_right _
  have hg : ∀ w, ∀ a b, (GlobalTheory.UnitaryBC.cEmb (B.emb w).1 k).1 a b = NormedSpace.exp (Y w) (Sum.inl a) (Sum.inl b) := fun w => by
    refine hlast w _ _ ?_
    have h1 := hgen 1 w
    rw [one_smul, hγ1] at h1
    rw [← he.emb w (B.emb w) k]
    exact h1
  obtain ⟨U, hU1, hU2⟩ := exp_gen_pk hact hadm hloc hγ hgen
  have e2 := isExp_unique_pk hU1 (UpperTheory.TP.RP.expSum _ _ (fun w => hloc _ _) fun w => hU w (Y w) _ (hg w))
  have := hU2 T
  rwa [hγ1, e2] at this
/- English proof (translation)
Use `set i₀ : Ix N 0 := Sum.inl ⟨0, hN⟩`. Use `set z : ℂ := 2 * Real.pi * Complex.I`. Use `set Y₀ : Mat N 0 := Matrix.diagonal (Pi.single i₀ z)`. Use `set Y : InfinitePlace (maximalRealSubfield E) → Mat N 0 := Pi.single w Y₀`. Establish `htr : Y₀.trace = z` using `by simp [Y₀, Matrix.trace_diagonal]`.

Establish `hexp0 : NormedSpace.exp Y₀ = 1`. Rewrite using `[Matrix.exp_diagonal, ← Matrix.diagonal_one]`. Use `congr 1`. Use function extensionality and compare the values at `a`. Rewrite using `[show NormedSpace.exp (Pi.single i₀ z : Ix N 0 → ℂ) a = NormedSpace.exp ((Pi.single i₀ z : Ix N 0 → ℂ) a) from Pi.coe_exp _ a]`.

Distinguish the cases in `h : a = i₀`. Substitute `h` using the available equality. Simplify using `[z, ← Complex.exp_eq_exp_ℂ, Complex.exp_two_pi_mul_I]`. Simplify using `[Pi.single_eq_of_ne h, NormedSpace.exp_zero]`. Establish `hs : Y₀ᴴ = -Y₀`.

Rewrite using `[Matrix.diagonal_conjTranspose, show -Y₀ = Matrix.diagonal (fun i => -(Pi.single i₀ z : Ix N 0 → ℂ) i) from Matrix.diagonal_neg _]`. Use `congr 1`. Use function extensionality and compare the values at `a`. Distinguish the cases in `h : a = i₀`. Substitute `h` using the available equality.

Simplify using `[z]`. Simplify using `[Pi.single_eq_of_ne h]`. Establish `hexp : ∀ w', NormedSpace.exp ((1 : ℝ) • Y w') = 1` using `fun w' => by`. Rewrite using `[one_smul]`. Distinguish the cases in `h : w' = w`.

Substitute `h` using the available equality. Simplify `hexp0` using `[Y]`. Simplify using `[Y, Pi.single_eq_of_ne h, NormedSpace.exp_zero]`. Take `⟨γ, hγ, hgen⟩` from `Main.i_lineex (maximalRealSubfield E) E (UpperTheory.TP.cj E) (Fin N) N 0 B.emb (incM _ W.J) b C hcm hC Y fun w' => GlobalTheory.FockKStab.mem_upq (isKC_all_pk _) (by`. Distinguish the cases in `h : w' = w`.

Substitute `h` using the available equality. Simplify `hs` using `[Y]`. Simplify using `[Y, Pi.single_eq_of_ne h])`. Establish `h1 : γ (Multiplicative.ofAdd 1) = 1` using `eq_one_of_frame_pk hcm hC (hγ.2 _) fun w' => by`. Use `hgen 1 w'` as an intermediate fact.

Rewrite `this` using `[hexp w', Matrix.mul_one]`. Conclude with `this`. Take `⟨U, hU1, hU2⟩` from `exp_gen_pk hact hadm hloc hγ hgen`. Use `set T₀ : Tens (maximalRealSubfield E) P Q R S := PiTensorProduct.tprod ℂ fun _ => 1`. Establish `hT0 : T₀ ≠ 0` using `UpperTheory.TP.RP.tprodNe _ fun _ => one_ne_zero`.

Establish `hfix : U T₀ = T₀`. Use `hΦ (GlobalTheory.FockBottom.acts_unique (hU2 T₀) ?_)` and prove the remaining obligations. Rewrite using `[h1, map_one]`. Conclude with `fun r _ => rfl`. Use `set μ : ℂ := ((D : ℂ) + m w) / 2 * z`.

Establish `hL : (sumPl fun w' => act (Y w') + (((m w' : ℂ) / 2) * (Y w').trace) • 1) T₀ = μ • T₀`. Establish `hsum : ∑ w', ((D : ℂ) / 2 + (m w' : ℂ) / 2) * (Y w').trace = μ`. Rewrite using `[Finset.sum_eq_single w]`. Simplify using `only [Y, Pi.single_eq_same, htr, μ]`. Expand and normalize the polynomial expressions, which then agree.

Introduce `w' _ h`. Simplify using `[Y, Pi.single_eq_of_ne h]`. Simplify using the standard rewrite rules. Use `sumPl_tprod_pk (fun w' => act (Y w') + (((m w' : ℂ) / 2) * (Y w').trace) • 1) (fun _ => (1 : Formalism.BasicNotions.TH.Pol P Q R S)) (fun w' => ((D : ℂ) / 2 + (m w' : ℂ) / 2) * (Y w').trace) fun w' => by` as an intermediate fact. Rewrite using `[LinearMap.add_apply, hvac, LinearMap.smul_apply, Module.End.one_apply, ← add_smul]`.

Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Rewrite `this` using `[hsum]`. Conclude with `this`. Establish `he` using `GlobalTheory.FockBottom.isExp_eig hU1 LinearMap.id _ (fun _ => rfl) (T := T₀) (μ := μ) hL`.

Simplify using `only [LinearMap.id_apply] at he`. Rewrite `he` using `[hfix]`. Establish `h2 : Complex.exp μ = 1`. Assume the negation of the conclusion as `hne`. Establish `: (1 - Complex.exp μ) • T₀ = 0` using `by rw [sub_smul, one_smul, ← he, sub_self]`.

Break down `smul_eq_zero.1 this with h | h` into its components or cases. Conclude with `hne (sub_eq_zero.1 h).symm`. Conclude with `hT0 h`. Take `⟨a, ha⟩` from `Complex.exp_eq_one_iff.1 h2`. Use `⟨a, ?_⟩` and prove the remaining obligations.

Establish `hz : z ≠ 0` using `by simp [z, Real.pi_ne_zero]`. Establish `h3 : ((D : ℂ) + m w) / 2 = a` using `mul_right_cancel₀ hz (by simpa [μ, z] using ha)`. Establish `h4 : (2 * a : ℂ) = D + m w` using `by rw [← h3]; ring`. Conclude with `h4` after adjusting the coercions.
-/
private theorem parity_of_pk (hcm : IsCMExt (maximalRealSubfield E) E (UpperTheory.TP.cj E)) {B : Base (maximalRealSubfield E) E} {N : ℕ}
    {W : Spc (maximalRealSubfield E) E N} {b : ℂ} (hN : 1 ≤ N)
    {C : InfinitePlace (maximalRealSubfield E) → Matrix (Fin N) (Ix N 0) ℂ}
    (hC : ∀ w, IsFrame (b • (incM (maximalRealSubfield E) W.J).map (piInf (B.emb w))) (C w))
    {Φ : Tens (maximalRealSubfield E) P Q R S →ₗ[ℂ] SInf (maximalRealSubfield E) (Fin n × Fin d)} (hΦ : Function.Injective Φ)
    {om' : UA (UpperTheory.TP.cj E) W.J →* Module.End ℂ ((Fin n × Fin d → AF (maximalRealSubfield E)) → ℂ)}
    {act : Mat N 0 →ₗ[ℂ] Module.End ℂ (Formalism.BasicNotions.TH.Pol P Q R S)} {m : InfinitePlace (maximalRealSubfield E) → ℤ}
    (hact : ActsBy B.emb C om' Φ act fun w => (m w : ℂ) / 2)
    (hadm : ∀ g, ∀ l ∈ (adeleClass (maximalRealSubfield E)).adm (Fin n × Fin d),
      l ∘ₗ om' g ∈ (adeleClass (maximalRealSubfield E)).adm (Fin n × Fin d))
    (hloc : ∀ (Y : Mat N 0) (z : ℂ), LocFin (act Y + z • 1)) (D : ℕ)
    (hvac : ∀ Y : Mat N 0, act Y (1 : Formalism.BasicNotions.TH.Pol P Q R S) = (((D : ℂ) / 2) * Y.trace) • (1 : Formalism.BasicNotions.TH.Pol P Q R S))
    (w : InfinitePlace (maximalRealSubfield E)) : ∃ a : ℤ, 2 * a = D + m w := by
  set i₀ : Ix N 0 := Sum.inl ⟨0, hN⟩
  set z : ℂ := 2 * Real.pi * Complex.I
  set Y₀ : Mat N 0 := Matrix.diagonal (Pi.single i₀ z)
  set Y : InfinitePlace (maximalRealSubfield E) → Mat N 0 := Pi.single w Y₀
  have htr : Y₀.trace = z := by simp [Y₀, Matrix.trace_diagonal]
  have hexp0 : NormedSpace.exp Y₀ = 1 := by
    rw [Matrix.exp_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext a
    rw [show NormedSpace.exp (Pi.single i₀ z : Ix N 0 → ℂ) a = NormedSpace.exp ((Pi.single i₀ z : Ix N 0 → ℂ) a) from Pi.coe_exp _ a]
    by_cases h : a = i₀
    · subst h
      simp [z, ← Complex.exp_eq_exp_ℂ, Complex.exp_two_pi_mul_I]
    · simp [Pi.single_eq_of_ne h, NormedSpace.exp_zero]
  have hs : Y₀ᴴ = -Y₀ := by
    rw [Matrix.diagonal_conjTranspose, show -Y₀ = Matrix.diagonal (fun i => -(Pi.single i₀ z : Ix N 0 → ℂ) i) from Matrix.diagonal_neg _]
    congr 1
    funext a
    by_cases h : a = i₀
    · subst h
      simp [z]
    · simp [Pi.single_eq_of_ne h]
  have hexp : ∀ w', NormedSpace.exp ((1 : ℝ) • Y w') = 1 := fun w' => by
    rw [one_smul]
    by_cases h : w' = w
    · subst h; simpa [Y] using hexp0
    · simp [Y, Pi.single_eq_of_ne h, NormedSpace.exp_zero]
  obtain ⟨γ, hγ, hgen⟩ := Main.i_lineex (maximalRealSubfield E) E (UpperTheory.TP.cj E) (Fin N) N 0 B.emb (incM _ W.J) b C hcm hC Y fun w' =>
    GlobalTheory.FockKStab.mem_upq (isKC_all_pk _) (by
      by_cases h : w' = w
      · subst h; simpa [Y] using hs
      · simp [Y, Pi.single_eq_of_ne h])
  have h1 : γ (Multiplicative.ofAdd 1) = 1 := eq_one_of_frame_pk hcm hC (hγ.2 _) fun w' => by
    have := hgen 1 w'
    rw [hexp w', Matrix.mul_one] at this
    exact this
  obtain ⟨U, hU1, hU2⟩ := exp_gen_pk hact hadm hloc hγ hgen
  set T₀ : Tens (maximalRealSubfield E) P Q R S := PiTensorProduct.tprod ℂ fun _ => 1
  have hT0 : T₀ ≠ 0 := UpperTheory.TP.RP.tprodNe _ fun _ => one_ne_zero
  have hfix : U T₀ = T₀ := by
    refine hΦ (GlobalTheory.FockBottom.acts_unique (hU2 T₀) ?_)
    rw [h1, map_one]
    exact fun r _ => rfl
  set μ : ℂ := ((D : ℂ) + m w) / 2 * z
  have hL : (sumPl fun w' => act (Y w') + (((m w' : ℂ) / 2) * (Y w').trace) • 1) T₀ = μ • T₀ := by
    have hsum : ∑ w', ((D : ℂ) / 2 + (m w' : ℂ) / 2) * (Y w').trace = μ := by
      rw [Finset.sum_eq_single w]
      · simp only [Y, Pi.single_eq_same, htr, μ]; ring
      · intro w' _ h
        simp [Y, Pi.single_eq_of_ne h]
      · simp
    have := sumPl_tprod_pk (fun w' => act (Y w') + (((m w' : ℂ) / 2) * (Y w').trace) • 1)
      (fun _ => (1 : Formalism.BasicNotions.TH.Pol P Q R S)) (fun w' => ((D : ℂ) / 2 + (m w' : ℂ) / 2) * (Y w').trace) fun w' => by
        rw [LinearMap.add_apply, hvac, LinearMap.smul_apply, Module.End.one_apply, ← add_smul]
        congr 1; ring
    rw [hsum] at this
    exact this
  have he := GlobalTheory.FockBottom.isExp_eig hU1 LinearMap.id _ (fun _ => rfl) (T := T₀) (μ := μ) hL
  simp only [LinearMap.id_apply] at he
  rw [hfix] at he
  have h2 : Complex.exp μ = 1 := by
    by_contra hne
    have : (1 - Complex.exp μ) • T₀ = 0 := by rw [sub_smul, one_smul, ← he, sub_self]
    rcases smul_eq_zero.1 this with h | h
    · exact hne (sub_eq_zero.1 h).symm
    · exact hT0 h
  obtain ⟨a, ha⟩ := Complex.exp_eq_one_iff.1 h2
  refine ⟨a, ?_⟩
  have hz : z ≠ 0 := by simp [z, Real.pi_ne_zero]
  have h3 : ((D : ℂ) + m w) / 2 = a := mul_right_cancel₀ hz (by simpa [μ, z] using ha)
  have h4 : (2 * a : ℂ) = D + m w := by rw [← h3]; ring
  exact_mod_cast h4
end CM
end UpperTheory.TP.RP.FockModelActions
end
open UpperTheory.TP.RP.FockModelActions in
/- English proof (translation)
Introduce `T E _ _ _ B n d X W M χX χW om hP hn hnd e e' he he' δ mX mW hXJ hWJ eX eW`. Take `⟨A, C, fr, hAθ, hCθ, hA', hC'⟩` from `UpperTheory.TP.RP.frames E B n d X W δ hP.herm hP.skew hXJ hWJ`. Establish `hb` using `hP.base`. Take `⟨Φ, hΦ⟩` from `Main.i_fockex Main.i_derex _ E (UpperTheory.TP.cj E) _ _ _ n 0 d 0 B.ψ B.emb _ _ M.co 1 Complex.I A C hb.cm hb.std fr`. Establish `hr` using `Main.i_polrange Main.i_actslaws Main.i_derex (Main.i_vacline Main.i_derex) _ E (UpperTheory.TP.cj E) _ _ _ _ _ _ X W M B.ψ B.emb A C Φ hb.cm hb.std fr hAθ hCθ hΦ`.

Establish `hwp : IsUWeilPair (cA (UpperTheory.TP.cj E)) (adeleClass (maximalRealSubfield E)) B.ψ (-1) (incM (maximalRealSubfield E) X.J) (incM (maximalRealSubfield E) W.J) M.co χX χW om` using `hP.weil`. Take `⟨d', hd', hB1⟩` from `hwp.2.1`. Establish `hW1` using `T.lie1 _ E (UpperTheory.TP.cj E) _ _ _ _ _ _ _ B.ψ B.emb _ _ M.co d' 1 Complex.I A C Φ _ χW mW hb.cm hb.std fr hΦ hd' hB1 eW`. Establish `hX1` using `T.lie2 _ E (UpperTheory.TP.cj E) _ _ _ _ _ _ _ B.ψ B.emb _ _ M.co 1 Complex.I A C Φ _ χX mX hb.cm hb.std fr hΦ hwp.1 eX`. Establish `hadm1 : ∀ g, ∀ l ∈ (adeleClass (maximalRealSubfield E)).adm (Fin n × Fin d), l ∘ₗ (om.comp (MonoidHom.inl _ _)) g ∈ (adeleClass (maximalRealSubfield E)).adm (Fin n × Fin d)` using `fun g => (hwp.isUSplitting).adm _`.

Establish `hadm2 : ∀ g, ∀ l ∈ (adeleClass (maximalRealSubfield E)).adm (Fin n × Fin d), l ∘ₗ (om.comp (MonoidHom.inr _ _)) g ∈ (adeleClass (maximalRealSubfield E)).adm (Fin n × Fin d)` using `fun g => (hwp.isUSplitting).adm _`. Establish `hloc1 : ∀ (Y : Mat n 0) (z : ℂ), LocFin (fockAct1 n 0 d 0 Y + z • 1)` using `fun Y z => Main.locFin_fock1 n 0 d 0 Y (isKC_all_pk Y) z`. Establish `hloc2 : ∀ (Y : Mat d 0) (z : ℂ), LocFin (fockAct2 n 0 d 0 Y + z • 1)` using `fun Y z => Main.locFin_fock2 n 0 d 0 Y (isKC_all_pk Y) z`. Use `choose a ha using parity_of_pk hb.cm hn fr.2.1 hΦ.1 hW1 hadm1 hloc1 d fock_first_action_one_polynomial`. Use `choose b hb' using parity_of_pk hb.cm (hn.trans hnd) fr.2.2 hΦ.1 hX1 hadm2 hloc2 n fock_second_action_one_polynomial`.

Use `⟨Φ, a, b, hΦ.1, hr, ha, hb', ?_, ?_⟩` and prove the remaining obligations. Conclude with `acts_of_k_pk hb.cm he fr.2.1 hAθ hA' hW1 hadm1 hloc1 (fun w g => act1 (a w) g) fun w Y g hg => UpperTheory.TP.RP.expFirst Y g (a w) _ hg (by`. Establish `: (2 * a w : ℂ) = d + mW w` using `by exact_mod_cast ha w`. Rewrite using `[this]`. Use the proof step `ring)`.

Conclude with `acts_of_k_pk hb.cm he' fr.2.2 hCθ hC' hX1 hadm2 hloc2 (fun w g => act2 (b w) g) fun w Y g hg => UpperTheory.TP.RP.expSecond Y g (b w) _ hg (by`. Establish `: (2 * b w : ℂ) = n + mX w` using `by exact_mod_cast hb' w`. Rewrite using `[this]`. Use the proof step `ring)`.
-/
theorem UpperTheory.TP.RP.fockOf_k :
    _root_.UpperTheory.TP.Tools_k → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (B : Base (maximalRealSubfield E) E) (n d : ℕ) (X : Spc (maximalRealSubfield E) E n) (W : Spc (maximalRealSubfield E) E d)
      (M : Model (UpperTheory.TP.cj E) X W) (χX χW : Chr (maximalRealSubfield E) E) (om : Rep (UpperTheory.TP.cj E) X W), _root_.GlobalTheory.ThK.IsPair_k B M χX χW om n 0 d 0 → 1 ≤ n → n ≤ d →
      ∀ (e : GlobalTheory.UnitaryBC.UA E n ≃ₜ* UA (UpperTheory.TP.cj E) X.J) (e' : GlobalTheory.UnitaryBC.UA E d ≃ₜ* UA (UpperTheory.TP.cj E) W.J), UpperTheory.TP.IsBr X e → UpperTheory.TP.IsBr W e' →
      ∀ (δ : E) (mX mW : InfinitePlace (maximalRealSubfield E) → ℤ), X.J = 1 → W.J = δ • (1 : Matrix (Fin d) (Fin d) E) → HasExp B.emb χX mX → HasExp B.emb χW mW →
      ∃ (Φ : Tens (maximalRealSubfield E) n 0 d 0 →ₗ[ℂ] SInf (maximalRealSubfield E) (Fin n × Fin d)) (a b : InfinitePlace (maximalRealSubfield E) → ℤ),
        Function.Injective Φ ∧ LinearMap.range Φ = M.Pol B.ψ B.emb ∧ (∀ w, 2 * a w = d + mW w) ∧ (∀ w, 2 * b w = n + mX w) ∧
        (∀ k ∈ GlobalTheory.UnitaryBC.infU E n, ∀ T, Acts (evI (maximalRealSubfield E)) (om (e k, 1)) (Φ T)
          (Φ (PiTensorProduct.map (fun w => (act1 (a w) (GlobalTheory.UnitaryBC.cEmb (B.emb w).1 k) : Module.End ℂ (PP n d))) T))) ∧
        ∀ k ∈ GlobalTheory.UnitaryBC.infU E d, ∀ T, Acts (evI (maximalRealSubfield E)) (om (1, e' k)) (Φ T)
          (Φ (PiTensorProduct.map (fun w => (act2 (b w) (GlobalTheory.UnitaryBC.cEmb (B.emb w).1 k) : Module.End ℂ (PP n d))) T)) := by
  intro T E _ _ _ B n d X W M χX χW om hP hn hnd e e' he he' δ mX mW hXJ hWJ eX eW
  obtain ⟨A, C, fr, hAθ, hCθ, hA', hC'⟩ := UpperTheory.TP.RP.frames E B n d X W δ hP.herm hP.skew hXJ hWJ
  have hb := hP.base
  obtain ⟨Φ, hΦ⟩ := Main.i_fockex Main.i_derex _ E (UpperTheory.TP.cj E) _ _ _ n 0 d 0 B.ψ B.emb _ _ M.co 1 Complex.I A C hb.cm hb.std fr
  have hr := Main.i_polrange Main.i_actslaws Main.i_derex (Main.i_vacline Main.i_derex) _ E (UpperTheory.TP.cj E) _ _ _ _ _ _ X W M B.ψ B.emb A C Φ
    hb.cm hb.std fr hAθ hCθ hΦ
  have hwp : IsUWeilPair (cA (UpperTheory.TP.cj E)) (adeleClass (maximalRealSubfield E)) B.ψ (-1) (incM (maximalRealSubfield E) X.J)
    (incM (maximalRealSubfield E) W.J) M.co χX χW om := hP.weil
  obtain ⟨d', hd', hB1⟩ := hwp.2.1
  have hW1 := T.lie1 _ E (UpperTheory.TP.cj E) _ _ _ _ _ _ _ B.ψ B.emb _ _ M.co d' 1 Complex.I A C Φ _ χW mW hb.cm hb.std fr hΦ hd' hB1 eW
  have hX1 := T.lie2 _ E (UpperTheory.TP.cj E) _ _ _ _ _ _ _ B.ψ B.emb _ _ M.co 1 Complex.I A C Φ _ χX mX hb.cm hb.std fr hΦ hwp.1 eX
  have hadm1 : ∀ g, ∀ l ∈ (adeleClass (maximalRealSubfield E)).adm (Fin n × Fin d),
      l ∘ₗ (om.comp (MonoidHom.inl _ _)) g ∈ (adeleClass (maximalRealSubfield E)).adm (Fin n × Fin d) :=
    fun g => (hwp.isUSplitting).adm _
  have hadm2 : ∀ g, ∀ l ∈ (adeleClass (maximalRealSubfield E)).adm (Fin n × Fin d),
      l ∘ₗ (om.comp (MonoidHom.inr _ _)) g ∈ (adeleClass (maximalRealSubfield E)).adm (Fin n × Fin d) :=
    fun g => (hwp.isUSplitting).adm _
  have hloc1 : ∀ (Y : Mat n 0) (z : ℂ), LocFin (fockAct1 n 0 d 0 Y + z • 1) := fun Y z => Main.locFin_fock1 n 0 d 0 Y (isKC_all_pk Y) z
  have hloc2 : ∀ (Y : Mat d 0) (z : ℂ), LocFin (fockAct2 n 0 d 0 Y + z • 1) := fun Y z => Main.locFin_fock2 n 0 d 0 Y (isKC_all_pk Y) z
  choose a ha using parity_of_pk hb.cm hn fr.2.1 hΦ.1 hW1 hadm1 hloc1 d fock_first_action_one_polynomial
  choose b hb' using parity_of_pk hb.cm (hn.trans hnd) fr.2.2 hΦ.1 hX1 hadm2 hloc2 n fock_second_action_one_polynomial
  refine ⟨Φ, a, b, hΦ.1, hr, ha, hb', ?_, ?_⟩
  · exact acts_of_k_pk hb.cm he fr.2.1 hAθ hA' hW1 hadm1 hloc1 (fun w g => act1 (a w) g) fun w Y g hg =>
      UpperTheory.TP.RP.expFirst Y g (a w) _ hg (by
        have : (2 * a w : ℂ) = d + mW w := by exact_mod_cast ha w
        rw [this]; ring)
  · exact acts_of_k_pk hb.cm he' fr.2.2 hCθ hC' hX1 hadm2 hloc2 (fun w g => act2 (b w) g) fun w Y g hg =>
      UpperTheory.TP.RP.expSecond Y g (b w) _ hg (by
        have : (2 * b w : ℂ) = n + mX w := by exact_mod_cast hb' w
        rw [this]; ring)
end
