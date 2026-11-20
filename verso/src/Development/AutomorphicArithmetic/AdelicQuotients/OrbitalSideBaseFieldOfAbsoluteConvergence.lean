import Development.AutomorphicArithmetic.Foundations.Convolution.LocalGroupAnalysis.SelmerRankBoundLaurent
open PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory.G UpperTheory.ConvolutionTheory.T4

open MeasureTheory NumberField IsDedekindDomain Topology Filter GroundTheory.Automorphic GroundTheory.Automorphic.Reduction in
/- English proof (translation)
Introduce `hS hRP hRC hUL hUO hTC hSep hCL hInf F _ _ n hn _ _ _ _ μ μi m hμ hμi hm γ hγ ν νi nv hν hνi hnv S a b ha hb hT hE fi f hfi hfc hf hloc`. Establish `hcA : IsClosed ((TA γ : Subgroup (GA F n)) : Set (GA F n))` using `Set.isClosed_centralizer _`. Establish `hcI : IsClosed ((TI γ : Subgroup (GL (Fin n) (InfiniteAdeleRing F))) : Set (GL (Fin n) (InfiniteAdeleRing F)))` using `Set.isClosed_centralizer _`. Establish `hcF : ∀ v : Pl F, IsClosed ((TF γ v : Subgroup (GL (Fin n) (v.adicCompletion F))) : Set (GL (Fin n) (v.adicCompletion F)))` using `fun v => Set.isClosed_centralizer _`. Use `haveI : LocallyCompactSpace (TA γ) := hcA.locallyCompactSpace`.

Use `haveI : LocallyCompactSpace (TI γ) := hcI.locallyCompactSpace`. Use `haveI : ∀ v : Pl F, LocallyCompactSpace (TF γ v) := fun v => (hcF v).locallyCompactSpace`. Use `haveI : SecondCountableTopology (TA γ) := TopologicalSpace.Subtype.secondCountableTopology ((TA γ : Subgroup (GA F n)) : Set (GA F n))`. Use `haveI : SecondCountableTopology (TI γ) := TopologicalSpace.Subtype.secondCountableTopology ((TI γ : Subgroup (GL (Fin n) (InfiniteAdeleRing F))) : Set (GL (Fin n) (InfiniteAdeleRing F)))`. Use `haveI : ∀ v : Pl F, SecondCountableTopology (TF γ v) := fun v => TopologicalSpace.Subtype.secondCountableTopology ((TF γ v : Subgroup (GL (Fin n) (v.adicCompletion F))) : Set (GL (Fin n) (v.adicCompletion F)))`.

Establish `hR` using `hRP F n`. Establish `hRT` using `hRC _ _ _ _ (pI F n) (pF F n) (KF F n) hR (AdelicGLn.diagonal F n γ)`. Take `⟨hc1, hc2, hc3, -⟩` from `hTC F n γ hγ`. Take `⟨hUi, hUv⟩` from `hUL (Pl F) (GA F n) _ _ (pI F n) (pF F n) (KF F n) hR μ μi m hμ hμi hm`. Establish `hP : Pair μ (TA γ).subtype ν` using `⟨hμ, hcA.isClosedEmbedding_subtypeVal, (hUO _ ν hν).2 hc1⟩`.

Establish `hPi : Pair μi (TI γ).subtype νi` using `⟨hUi, hcI.isClosedEmbedding_subtypeVal, (hUO _ νi hνi).2 hc2⟩`. Establish `hPv : ∀ v : Pl F, Pair (m v) (TF γ v).subtype (nv v)` using `fun v => ⟨hUv v, (hcF v).isClosedEmbedding_subtypeVal, (hUO _ (nv v) (hnv v)).2 (hc3 v)⟩`. Establish `hz : Continuous (zA F n)` using `(continuous_centralSection (K := F) (n := n)).comp (Continuous.subtype_mk Real.continuous_exp fun s => Real.exp_pos s)`. Establish `hzv : ∀ (v : Pl F) (s : ℝ), pF F n v (zA F n s) = 1` using `fun v s => (hCL F n _).2.2.1 v`. Establish `hfix : ∀ t : TA γ, ((TA γ).subtype t)⁻¹ * AdelicGLn.diagonal F n γ * (MonoidHom.id (GA F n)) ((TA γ).subtype t) = AdelicGLn.diagonal F n γ`.

Introduce `t`. Establish `h` using `Subgroup.mem_centralizer_singleton_iff.1 t.2`. Simplify using `only [Subgroup.subtype_apply, MonoidHom.id_apply]`. Use `first`. Consider the case `rw [mul_assoc, ← h, inv_mul_cancel_left]`.

Consider the case `rw [mul_assoc, h, inv_mul_cancel_left]`. Establish `hcpt : ∀ D : Set (GL (Fin n) (InfiniteAdeleRing F)), IsCompact D → ∃ C : Set (GL (Fin n) (InfiniteAdeleRing F)), IsCompact C ∧ ∀ x, x⁻¹ * pI F n (AdelicGLn.diagonal F n γ) * (MonoidHom.id _) x ∈ D → ∃ t : TI γ, ∃ y ∈ C, x = (TI γ).subtype t * y`. Introduce `D hD`. Take `⟨C, hC, h⟩` from `(hInf F n hn (pI F n (AdelicGLn.diagonal F n γ))).2 (hSep F n γ hγ).1 D hD`. Use `⟨C, hC, fun x hx => ?_⟩` and prove the remaining obligations.

Take `⟨t, ht, y, hy, rfl⟩` from `h x hx`. Apply the tactic sequence `exact ⟨⟨t, Subgroup.mem_centralizer_singleton_iff.2 (by first | exact ht | exact ht.symm)⟩, y, hy, rfl⟩`. Establish `hbd : ∀ D : Set (GL (Fin n) (InfiniteAdeleRing F)), IsCompact D → ∃ B : Set ℝ, IsCompact B ∧ ∀ s x, pI F n (zA F n s) * (x⁻¹ * pI F n (AdelicGLn.diagonal F n γ) * (MonoidHom.id _) x) ∈ D → s ∈ B` using `(hInf F n hn (pI F n (AdelicGLn.diagonal F n γ))).1`. Establish `hl : ∀ v ∉ S, f v = (KF F n v : Set (GL (Fin n) (v.adicCompletion F))).indicator 1 ∧ ∀ x, x⁻¹ * pF F n v (AdelicGLn.diagonal F n γ) * (MonoidHom.id _) x ∈ KF F n v ↔ ∃ t : TF γ v, ∃ y ∈ KF F n v, x = (TF γ v).subtype t * y`. Introduce `v hv`.

Use `⟨(hloc v hv).1, fun x => ?_⟩` and prove the remaining obligations. Use `((hloc v hv).2 x).trans ⟨?_, ?_⟩` and prove the remaining obligations. Introduce and unpack `⟨t, ht, y, hy, rfl⟩`. Apply the tactic sequence `exact ⟨⟨t, Subgroup.mem_centralizer_singleton_iff.2 (by first | exact ht | exact ht.symm)⟩, y, hy, rfl⟩`. Introduce and unpack `⟨t, y, hy, rfl⟩`.

Establish `h` using `Subgroup.mem_centralizer_singleton_iff.1 t.2`. Apply the tactic sequence `exact ⟨t, by first | exact h | exact h.symm, y, hy, rfl⟩`. Take `⟨hm1, hm2⟩` from `hS (Pl F) (GA F n) (GL (Fin n) (InfiniteAdeleRing F)) (fun v => GL (Fin n) (v.adicCompletion F)) (pI F n) (pF F n) (KF F n) (TA γ) (TI γ) (fun v => TF γ v) (cen (pI F n) (AdelicGLn.diagonal F n γ)) (fun v => cen (pF F n v) (AdelicGLn.diagonal F n γ)) (fun v => (KF F n v).comap (T …`. Use `⟨hm1, ?_⟩` and prove the remaining obligations. Use `Eq.trans hm2 ?_` and prove the remaining obligations.

Use `congr 3`. Use function extensionality and compare the values at `s`. Use `congr 1`. Use function extensionality and compare the values at `x`. Establish `hc` using `(hCL F n ⟨Real.exp s, Real.exp_pos s⟩).2.1`.

Use `congr 1`. Express the relevant statement in the definitionally equal form `pI F n (zA F n s) * (x⁻¹ * pI F n (AdelicGLn.diagonal F n γ) * x) = x⁻¹ * (pI F n (zA F n s) * pI F n (AdelicGLn.diagonal F n γ)) * x`. Rewrite using `[mul_assoc, mul_assoc, ← mul_assoc (pI F n (zA F n s)), hc x⁻¹, mul_assoc, mul_assoc]`.
-/
theorem UpperTheory.orbitalSideBaseField_of_absoluteConvergence :
    SideAbs → RPF → RPCen → UniLoc → UniOf → TComm → SepLoc → CentLoc → InfF → SideF := by
  intro hS hRP hRC hUL hUO hTC hSep hCL hInf F _ _ n hn _ _ _ _ μ μi m hμ hμi hm γ hγ ν νi nv hν hνi hnv S a b ha hb hT hE
    fi f hfi hfc hf hloc
  have hcA : IsClosed ((TA γ : Subgroup (GA F n)) : Set (GA F n)) := Set.isClosed_centralizer _
  have hcI : IsClosed ((TI γ : Subgroup (GL (Fin n) (InfiniteAdeleRing F))) : Set (GL (Fin n) (InfiniteAdeleRing F))) :=
    Set.isClosed_centralizer _
  have hcF : ∀ v : Pl F, IsClosed ((TF γ v : Subgroup (GL (Fin n) (v.adicCompletion F))) :
      Set (GL (Fin n) (v.adicCompletion F))) := fun v => Set.isClosed_centralizer _
  haveI : LocallyCompactSpace (TA γ) := hcA.locallyCompactSpace
  haveI : LocallyCompactSpace (TI γ) := hcI.locallyCompactSpace
  haveI : ∀ v : Pl F, LocallyCompactSpace (TF γ v) := fun v => (hcF v).locallyCompactSpace
  haveI : SecondCountableTopology (TA γ) :=
    TopologicalSpace.Subtype.secondCountableTopology ((TA γ : Subgroup (GA F n)) : Set (GA F n))
  haveI : SecondCountableTopology (TI γ) := TopologicalSpace.Subtype.secondCountableTopology
    ((TI γ : Subgroup (GL (Fin n) (InfiniteAdeleRing F))) : Set (GL (Fin n) (InfiniteAdeleRing F)))
  haveI : ∀ v : Pl F, SecondCountableTopology (TF γ v) := fun v => TopologicalSpace.Subtype.secondCountableTopology
    ((TF γ v : Subgroup (GL (Fin n) (v.adicCompletion F))) : Set (GL (Fin n) (v.adicCompletion F)))
  have hR := hRP F n
  have hRT := hRC _ _ _ _ (pI F n) (pF F n) (KF F n) hR (AdelicGLn.diagonal F n γ)
  obtain ⟨hc1, hc2, hc3, -⟩ := hTC F n γ hγ
  obtain ⟨hUi, hUv⟩ := hUL (Pl F) (GA F n) _ _ (pI F n) (pF F n) (KF F n) hR μ μi m hμ hμi hm
  have hP : Pair μ (TA γ).subtype ν := ⟨hμ, hcA.isClosedEmbedding_subtypeVal, (hUO _ ν hν).2 hc1⟩
  have hPi : Pair μi (TI γ).subtype νi := ⟨hUi, hcI.isClosedEmbedding_subtypeVal, (hUO _ νi hνi).2 hc2⟩
  have hPv : ∀ v : Pl F, Pair (m v) (TF γ v).subtype (nv v) := fun v =>
    ⟨hUv v, (hcF v).isClosedEmbedding_subtypeVal, (hUO _ (nv v) (hnv v)).2 (hc3 v)⟩
  have hz : Continuous (zA F n) :=
    (continuous_centralSection (K := F) (n := n)).comp
      (Continuous.subtype_mk Real.continuous_exp fun s => Real.exp_pos s)
  have hzv : ∀ (v : Pl F) (s : ℝ), pF F n v (zA F n s) = 1 := fun v s => (hCL F n _).2.2.1 v
  have hfix : ∀ t : TA γ, ((TA γ).subtype t)⁻¹ * AdelicGLn.diagonal F n γ * (MonoidHom.id (GA F n)) ((TA γ).subtype t) =
      AdelicGLn.diagonal F n γ := by
    intro t
    have h := Subgroup.mem_centralizer_singleton_iff.1 t.2
    simp only [Subgroup.subtype_apply, MonoidHom.id_apply]
    first
      | rw [mul_assoc, ← h, inv_mul_cancel_left]
      | rw [mul_assoc, h, inv_mul_cancel_left]
  have hcpt : ∀ D : Set (GL (Fin n) (InfiniteAdeleRing F)), IsCompact D → ∃ C : Set (GL (Fin n) (InfiniteAdeleRing F)),
      IsCompact C ∧ ∀ x, x⁻¹ * pI F n (AdelicGLn.diagonal F n γ) * (MonoidHom.id _) x ∈ D →
        ∃ t : TI γ, ∃ y ∈ C, x = (TI γ).subtype t * y := by
    intro D hD
    obtain ⟨C, hC, h⟩ := (hInf F n hn (pI F n (AdelicGLn.diagonal F n γ))).2 (hSep F n γ hγ).1 D hD
    refine ⟨C, hC, fun x hx => ?_⟩
    obtain ⟨t, ht, y, hy, rfl⟩ := h x hx
    exact ⟨⟨t, Subgroup.mem_centralizer_singleton_iff.2 (by first | exact ht | exact ht.symm)⟩, y, hy, rfl⟩
  have hbd : ∀ D : Set (GL (Fin n) (InfiniteAdeleRing F)), IsCompact D → ∃ B : Set ℝ, IsCompact B ∧
      ∀ s x, pI F n (zA F n s) * (x⁻¹ * pI F n (AdelicGLn.diagonal F n γ) * (MonoidHom.id _) x) ∈ D → s ∈ B :=
    (hInf F n hn (pI F n (AdelicGLn.diagonal F n γ))).1
  have hl : ∀ v ∉ S, f v = (KF F n v : Set (GL (Fin n) (v.adicCompletion F))).indicator 1 ∧
      ∀ x, x⁻¹ * pF F n v (AdelicGLn.diagonal F n γ) * (MonoidHom.id _) x ∈ KF F n v ↔
        ∃ t : TF γ v, ∃ y ∈ KF F n v, x = (TF γ v).subtype t * y := by
    intro v hv
    refine ⟨(hloc v hv).1, fun x => ?_⟩
    refine ((hloc v hv).2 x).trans ⟨?_, ?_⟩
    · rintro ⟨t, ht, y, hy, rfl⟩
      exact ⟨⟨t, Subgroup.mem_centralizer_singleton_iff.2 (by first | exact ht | exact ht.symm)⟩, y, hy, rfl⟩
    · rintro ⟨t, y, hy, rfl⟩
      have h := Subgroup.mem_centralizer_singleton_iff.1 t.2
      exact ⟨t, by first | exact h | exact h.symm, y, hy, rfl⟩
  obtain ⟨hm1, hm2⟩ := hS (Pl F) (GA F n) (GL (Fin n) (InfiniteAdeleRing F)) (fun v => GL (Fin n) (v.adicCompletion F))
    (pI F n) (pF F n) (KF F n) (TA γ) (TI γ) (fun v => TF γ v)
    (cen (pI F n) (AdelicGLn.diagonal F n γ)) (fun v => cen (pF F n v) (AdelicGLn.diagonal F n γ))
    (fun v => (KF F n v).comap (TF γ v).subtype) hR hRT (TA γ).subtype (TI γ).subtype (fun v => (TF γ v).subtype)
    (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => Iff.rfl) μ μi m ν νi nv hP hPi hPv S a b ha hb hE hT
    (MonoidHom.id _) (MonoidHom.id _) (fun _ => MonoidHom.id _) (fun _ => rfl) (fun _ _ => rfl)
    continuous_id (fun _ => continuous_id) (AdelicGLn.diagonal F n γ) (zA F n) hz hzv hfix hcpt hbd fi f hfi hfc hf hl
  refine ⟨hm1, ?_⟩
  refine Eq.trans hm2 ?_
  congr 3
  funext s
  congr 1
  funext x
  have hc := (hCL F n ⟨Real.exp s, Real.exp_pos s⟩).2.1
  congr 1
  change pI F n (zA F n s) * (x⁻¹ * pI F n (AdelicGLn.diagonal F n γ) * x) =
    x⁻¹ * (pI F n (zA F n s) * pI F n (AdelicGLn.diagonal F n γ)) * x
  rw [mul_assoc, mul_assoc, ← mul_assoc (pI F n (zA F n s)), hc x⁻¹, mul_assoc, mul_assoc]
