import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.CTFrameMatMulGram
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.IsAdaptedEmpty
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.LeviNormalizesUnipotentVariant
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ArchimedeanIwasawaMinimalParabolic
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ContinuousConjBlockEmbeddingStatement
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.RationalUnipotentLeParabolic
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.IsotropicFrameRankLeWittIndexStatement
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.IsotropicFrameWittBoundStatement
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.RestrictedCuspConstantTermVanishStatement
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.RestrictedConstantTermCompatibleStatement
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.LeviInfUnipotentLeHermitianPartStatement
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.RestrictedAutomorphicInvarianceStatement
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.HermitianFormChangeOfBasisLieStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsContinuousAdelicUnitaryEmbedding
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstAlongCocompactUniqueStages
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuotientMeasureProductGroups
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Published GlobalTheory.Published.AutFin GlobalTheory.StdPar GlobalTheory.ThK.SmoothLev GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart
open GlobalTheory.UAut GlobalTheory.AdelicU GlobalTheory.SiegelSet

noncomputable section
namespace GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.Slice

/- English proof (translation)
Introduce `D V m X Y hW S T hST p hpT`. Take `⟨hcm, hherm⟩` from `GlobalTheory.Mem.Vol.cmData_isCMExt_and_gram_isHermND D.host.F D.host.E D.sp.cm`. Establish `hJ` using `hherm V`. Distinguish the cases in `hS : S = ∅`. Substitute `hS` using the available equality.

Conclude with `⟨1, one_mem _, p, by simp, by simp⟩`. Take `⟨a, ha, ha'⟩ : ∃ a ∈ S, ∀ k ∈ S, k ≤ a` from `⟨S.max' (Finset.nonempty_iff_ne_empty.2 hS), S.max'_mem _, fun k hk => S.le_max' k hk⟩`. Establish `hP` using `GlobalTheory.ConstTrans.unip_le_parFlag _ _ D.sp.cm.sig hcm _ V.gram hJ m X Y hW T S a hST ha ha' hpT`. Establish `hdec` using `(GlobalTheory.LeviFlag.levi_decomposition _ _ D.sp.cm.sig hcm _ V.gram hJ (a.val + 1) (initCols X a) (initCols Y a) (fun i => (S.filter fun k => k.val < i.val).card) (by rw [initCols, GlobalTheory.TieStd.cT_submatrix_mul, hW.xx]; ext; simp) (by rw [initCols, GlobalTheory.TieStd.c …`. Conclude with `Matrix.submatrix_one _ (Fin.castLE_injective a.2))).1`.

Take `⟨u, hu, l, hl, rfl, -⟩` from `hdec p hP`. Establish `hflag` using `GlobalTheory.TieStd.stdPar_eq_flag _ _ D.sp.cm.sig hcm _ V.gram hJ m X Y hW S (a.val + 1) a.2 (fun i => ⟨fun h => ⟨a, ha, Nat.lt_succ_iff.1 h⟩, fun ⟨k, hk, hik⟩ => Nat.lt_succ_iff.2 (le_trans hik (ha' k hk))⟩) (fun i => (S.filter fun k => k.val < i.val).card) (fun i => rfl)`. Conclude with `⟨u, hflag.1 ▸ hu, l, hflag.2.1 ▸ hl, rfl⟩`.
-/
theorem unip_split : ∀ (D : D7) (V : HSp D) (m : ℕ) (X Y : Matrix (Fin V.rank) (Fin m) D.host.E),
    GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig V.gram X Y → ∀ S T : Finset (Fin m), S ⊆ T →
      ∀ p ∈ unip D.sp.cm.sig V.gram X T, ∃ u ∈ unip D.sp.cm.sig V.gram X S, ∃ l ∈ levi D.sp.cm.sig V.gram X Y S, p = u * l := by
  intro D V m X Y hW S T hST p hpT
  obtain ⟨hcm, hherm⟩ := GlobalTheory.Mem.Vol.cmData_isCMExt_and_gram_isHermND D.host.F D.host.E D.sp.cm
  have hJ := hherm V
  by_cases hS : S = ∅
  · subst hS
    exact ⟨1, one_mem _, p, by simp, by simp⟩
  obtain ⟨a, ha, ha'⟩ : ∃ a ∈ S, ∀ k ∈ S, k ≤ a := ⟨S.max' (Finset.nonempty_iff_ne_empty.2 hS),
    S.max'_mem _, fun k hk => S.le_max' k hk⟩
  have hP := GlobalTheory.ConstTrans.unip_le_parFlag _ _ D.sp.cm.sig hcm _ V.gram hJ m X Y hW T S a hST ha ha' hpT
  have hdec := (GlobalTheory.LeviFlag.levi_decomposition _ _ D.sp.cm.sig hcm _ V.gram hJ (a.val + 1) (initCols X a) (initCols Y a)
    (fun i => (S.filter fun k => k.val < i.val).card)
    (by rw [initCols, GlobalTheory.TieStd.cT_submatrix_mul, hW.xx]; ext; simp)
    (by rw [initCols, GlobalTheory.TieStd.cT_submatrix_mul, hW.yy]; ext; simp)
    (by rw [initCols, initCols, GlobalTheory.TieStd.cT_submatrix_mul, hW.xy]
        exact Matrix.submatrix_one _ (Fin.castLE_injective a.2))).1
  obtain ⟨u, hu, l, hl, rfl, -⟩ := hdec p hP
  have hflag := GlobalTheory.TieStd.stdPar_eq_flag _ _ D.sp.cm.sig hcm _ V.gram hJ m X Y hW S (a.val + 1) a.2
    (fun i => ⟨fun h => ⟨a, ha, Nat.lt_succ_iff.1 h⟩, fun ⟨k, hk, hik⟩ =>
      Nat.lt_succ_iff.2 (le_trans hik (ha' k hk))⟩)
    (fun i => (S.filter fun k => k.val < i.val).card) (fun i => rfl)
  exact ⟨u, hflag.1 ▸ hu, l, hflag.2.1 ▸ hl, rfl⟩

/- English proof (translation)
Introduce `D θ V U ε fr W _ _ ρ c m X Y hW T V' ι hι hr s hs ψ hψ y hy hyc`. Take `⟨hcm, hJall⟩` from `GlobalTheory.Mem.Vol.cmData_isCMExt_and_gram_isHermND D.host.F D.host.E D.sp.cm`. Establish `hJ` using `hJall V`. Establish `hJ'` using `hJall V'`. Take `⟨s₀, hs₀c, hs₀, hs₀Q⟩` from `GlobalTheory.Mem.UnitaryEmb.exists_embHom D V V' ι hι`.

Establish `es : ∀ h, s h = s₀ h` using `fun h => (hs₀ h (s h)).1 (hs h)`. Establish `hsc : Continuous s`. Establish `: (s : GA D V' → GA D V) = s₀` using `funext es`. Rewrite using `[this]`. Conclude with `hs₀c`.

Establish `hsQ : ∀ γ ∈ GQ V', s γ ∈ GQ V` using `fun γ hγ => es γ ▸ hs₀Q γ hγ`. Take `⟨hup, hsurj, -⟩` from `GlobalTheory.T.orthogonal_subspace_unitary_embedding D V m X Y hW T V' ι hι hr s hs`. Establish `hψl : ∀ γ ∈ leftSub V X Y T, ∀ g, ψ (γ * g) = ψ g` using `hψ.1.1.left`. Establish `hψc : Continuous ψ` using `hψ.1.1.cont`. Establish `hfl : ∀ γ ∈ GQ V', ∀ g, (fun h => ψ (s h * y)) (γ * g) = (fun h => ψ (s h * y)) g` using `fun γ hγ g => by`.

Establish `h1 : s γ ∈ leftSub V X Y T` using `Subgroup.mem_sup_right ⟨hsQ γ hγ, GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.uPart_le_levi D V m X Y T (hup γ)⟩`. Express the relevant statement in the definitionally equal form `ψ (s (γ * g) * y) = ψ (s g * y)`. Rewrite using `[map_mul, mul_assoc, hψl _ h1]`. Take `⟨m', e, X', Y', hsl, hW'⟩` from `GlobalTheory.T.orthogonal_subspace_witt_frame_extension D V m X Y hW T V' ι hι hr`. Use `GlobalTheory.T.cusp_function_of_constant_terms_vanish D V' m' X' Y' hW' (GlobalTheory.T.isotropic_frame_rank_le_witt_index D V' m' X' Y' hW') _ hfl fun k => ?_` and prove the remaining obligations.

Establish `hκ : e k ∉ upTo T` using `(hsl.2.1 _).2 ⟨k, rfl⟩`. Establish `hκT : e k ∉ T` using `fun h => hκ ⟨_, h, le_rfl⟩`. Establish `hTT' : T ⊂ insert (e k) T` using `Finset.ssubset_insert hκT`. Establish `hψ0` using `hψ.2 _ hTT'`. Use `haveI := locallyCompact_unip hcm hJ' hW' {k}`.

Use `haveI := locallyCompact_unip hcm hJ hW (insert (e k) T)`. Establish `hle` using `GlobalTheory.StdPar.unip_mono_of_subset _ _ D.sp.cm.sig hcm _ V.gram hJ m X Y hW (insert (e k) T) T hTT'.1`. Establish `hs1` using `GlobalTheory.T.restricted_cusp_constant_term_vanish D V m X Y hW T V' ι hι hr m' e X' Y' hsl hW' s hs k`. Establish `hdown` using `GlobalTheory.T.restricted_constant_term_compatible D V m X Y hW T V' ι hι hr m' e X' Y' hsl hW' s hs k`. Establish `hdec : ∀ v ∈ unip D.sp.cm.sig V.gram X (insert (e k) T), ∃ u ∈ unip D.sp.cm.sig V'.gram X' {k}, v * (s u)⁻¹ ∈ unip D.sp.cm.sig V.gram X T` using `fun v hv => by`.

Take `⟨u, hu, l, hl, rfl⟩` from `unip_split D V m X Y hW T _ hTT'.1 v hv`. Establish `hl' : l ∈ unip D.sp.cm.sig V.gram X (insert (e k) T)`. Simplify using `using mul_mem (inv_mem (hle hu)) hv`. Take `⟨b, rfl⟩` from `hsurj l (GlobalTheory.T.levi_inf_unipotent_le_hermitian_part D V m X Y hW T _ hκ ⟨hl, hl'⟩)`. Conclude with `⟨b, hdown b hl', by simpa using hu⟩`.

Establish `hnorm : ∀ p ∈ unip D.sp.cm.sig V.gram X (insert (e k) T), ∀ a ∈ unip D.sp.cm.sig V.gram X T, p * a * p⁻¹ ∈ unip D.sp.cm.sig V.gram X T` using `fun p hp a ha => conj_mem_unip_of_subset hcm hJ hW hTT'.1 hp ha`. Take `⟨π, hπc, hπ, hπQ⟩` from `GlobalTheory.T.restricted_automorphic_invariance D V m X Y hW T V' ι hι hr s hs _ _ hnorm hdec`. Set `s₁ : unip D.sp.cm.sig V'.gram X' {k} →* unip D.sp.cm.sig V.gram X (insert (e k) T)` to `(s.comp (unip D.sp.cm.sig V'.gram X' {k}).subtype).codRestrict _ fun u => hs1 _ u.2`. Establish `hs₁c : Continuous s₁` using `(hsc.comp continuous_subtype_val).subtype_mk _`. Establish `hπs : ∀ u, π (s₁ u) = u` using `fun u => (hπ _ _).2 (by`.

Express the relevant statement in the definitionally equal form `s u * (s u)⁻¹ ∈ _`. Simplify using `[one_mem])`. Establish `hker : ∀ v, π v = 1 ↔ (v : GA D V) ∈ unip D.sp.cm.sig V.gram X T` using `fun v => by`. Rewrite using `[hπ v 1]`. Simplify using the standard rewrite rules.

Introduce `μ 𝓕 hμ h𝓕 h1 g`. Establish `cN : GlobalTheory.Cusp.Cocompact (GQ V) (unip D.sp.cm.sig V.gram X (insert (e k) T))` using `cocompact_unip_std hcm hJ hW _`. Establish `key` using `GlobalTheory.Cusp.constTermOn_eq_integral_semidirect (GA D V) (GA D V') (GQ V) _ _ (GQ V') _ hle cN (cocompact_unip_std hcm hJ hW T) (cocompact_unip_std hcm hJ' hW' {k}) s₁ π hs₁c hπc hπs hker (fun u hu => hsQ _ hu) (fun v hv => hπQ v hv) ψ hψc (fun a ha y => hψl a (Subgroup.mem_ …`. Take `⟨μ₀, 𝓕₀, a1, a2, a3⟩` from `exists_mass_one cN`. Establish `hz` using `hψ0 μ₀ 𝓕₀ a1 a2 a3 (s g * y)`.

Establish `hct : GlobalTheory.Cusp.constTermOn (GQ V) (unip D.sp.cm.sig V.gram X (insert (e k) T)) ψ (s g * y) = 0` using `by haveI := a1`. Establish `e1` using `GlobalTheory.Cusp.Stages.constTermOn_eq' (Γ := GQ V) (φ := ψ) (x := s g * y) a2 (fun γ hγ n => by`. Simplify using `only [Subgroup.coe_mul, mul_assoc]`. Conclude with `hψl _ (ratPts_unip_le_leftSub D V m X Y hW T _ hTT'.1 ⟨hγ, (γ : unip _ _ _ _).2⟩) _)`. Rewrite using `[e1, ← hz]`.

Simplify using the standard rewrite rules. Rewrite `key` using `[hct]`. Use `key.trans (MeasureTheory.integral_congr_ae (.of_forall fun u => ?_))` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `ψ (s u * (s g * y)) = ψ (s (u * g) * y)`. Rewrite using `[map_mul, mul_assoc]`.
-/
theorem isCuspFun_slice : ∀ (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D) (U : Subgroup (GA D V)) (ε : D.what₂.Tau → Fin V.rank → Bool) (fr : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) (W : D.what₂.Tau → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module ℂ (W τ)] (ρ : ∀ τ, Representation ℂ (Formalism.REAL.KG (ε τ)) (W τ)) (c : D.what₂.Tau → ℕ → ℂ) (m : ℕ) (X Y : Matrix (Fin V.rank) (Fin m) D.host.E), GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig V.gram X Y → ∀ (T : Finset (Fin m)) (V' : HSp D) (ι : V'.V →ₗ[D.host.E] V.V), HSpace.IsIsomEmb V' V ι → (∀ v : V.V, v ∈ LinearMap.range ι ↔ ∀ i ∈ GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.upTo T, V.hT (V.frame.equivFun.symm fun j => X j i) v = 0 ∧ V.hT (V.frame.equivFun.symm fun j => Y j i) v = 0) → ∀ s : GA D V' →* GA D V, (∀ h, EmbRel V V' ι (s h) h) → ∀ ψ ∈ cuspOn θ V X Y T U ε fr ρ c, ∀ y ∈ levi D.sp.cm.sig V.gram X Y T, (∀ t ∈ uPart D.sp.cm.sig V.gram X Y T, t * y = y * t) → IsCuspFun V' fun h => ψ (s h * y) := by
  intro D θ V U ε fr W _ _ ρ c m X Y hW T V' ι hι hr s hs ψ hψ y hy hyc
  obtain ⟨hcm, hJall⟩ := GlobalTheory.Mem.Vol.cmData_isCMExt_and_gram_isHermND D.host.F D.host.E D.sp.cm
  have hJ := hJall V
  have hJ' := hJall V'
  obtain ⟨s₀, hs₀c, hs₀, hs₀Q⟩ := GlobalTheory.Mem.UnitaryEmb.exists_embHom D V V' ι hι
  have es : ∀ h, s h = s₀ h := fun h => (hs₀ h (s h)).1 (hs h)
  have hsc : Continuous s := by
    have : (s : GA D V' → GA D V) = s₀ := funext es
    rw [this]; exact hs₀c
  have hsQ : ∀ γ ∈ GQ V', s γ ∈ GQ V := fun γ hγ => es γ ▸ hs₀Q γ hγ
  obtain ⟨hup, hsurj, -⟩ := GlobalTheory.T.orthogonal_subspace_unitary_embedding D V m X Y hW T V' ι hι hr s hs
  have hψl : ∀ γ ∈ leftSub V X Y T, ∀ g, ψ (γ * g) = ψ g := hψ.1.1.left
  have hψc : Continuous ψ := hψ.1.1.cont
  have hfl : ∀ γ ∈ GQ V', ∀ g, (fun h => ψ (s h * y)) (γ * g) = (fun h => ψ (s h * y)) g := fun γ hγ g => by
    have h1 : s γ ∈ leftSub V X Y T := Subgroup.mem_sup_right ⟨hsQ γ hγ,
      GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.uPart_le_levi D V m X Y T (hup γ)⟩
    change ψ (s (γ * g) * y) = ψ (s g * y)
    rw [map_mul, mul_assoc, hψl _ h1]
  obtain ⟨m', e, X', Y', hsl, hW'⟩ := GlobalTheory.T.orthogonal_subspace_witt_frame_extension D V m X Y hW T V' ι hι hr
  refine GlobalTheory.T.cusp_function_of_constant_terms_vanish D V' m' X' Y' hW' (GlobalTheory.T.isotropic_frame_rank_le_witt_index D V' m' X' Y' hW') _ hfl fun k => ?_
  have hκ : e k ∉ upTo T := (hsl.2.1 _).2 ⟨k, rfl⟩
  have hκT : e k ∉ T := fun h => hκ ⟨_, h, le_rfl⟩
  have hTT' : T ⊂ insert (e k) T := Finset.ssubset_insert hκT
  have hψ0 := hψ.2 _ hTT'
  haveI := locallyCompact_unip hcm hJ' hW' {k}
  haveI := locallyCompact_unip hcm hJ hW (insert (e k) T)
  have hle := GlobalTheory.StdPar.unip_mono_of_subset _ _ D.sp.cm.sig hcm _ V.gram hJ m X Y hW (insert (e k) T) T hTT'.1
  have hs1 := GlobalTheory.T.restricted_cusp_constant_term_vanish D V m X Y hW T V' ι hι hr m' e X' Y' hsl hW' s hs k
  have hdown := GlobalTheory.T.restricted_constant_term_compatible D V m X Y hW T V' ι hι hr m' e X' Y' hsl hW' s hs k
  have hdec : ∀ v ∈ unip D.sp.cm.sig V.gram X (insert (e k) T), ∃ u ∈ unip D.sp.cm.sig V'.gram X' {k},
      v * (s u)⁻¹ ∈ unip D.sp.cm.sig V.gram X T := fun v hv => by
    obtain ⟨u, hu, l, hl, rfl⟩ := unip_split D V m X Y hW T _ hTT'.1 v hv
    have hl' : l ∈ unip D.sp.cm.sig V.gram X (insert (e k) T) := by
      simpa using mul_mem (inv_mem (hle hu)) hv
    obtain ⟨b, rfl⟩ := hsurj l (GlobalTheory.T.levi_inf_unipotent_le_hermitian_part D V m X Y hW T _ hκ ⟨hl, hl'⟩)
    exact ⟨b, hdown b hl', by simpa using hu⟩
  have hnorm : ∀ p ∈ unip D.sp.cm.sig V.gram X (insert (e k) T), ∀ a ∈ unip D.sp.cm.sig V.gram X T,
      p * a * p⁻¹ ∈ unip D.sp.cm.sig V.gram X T := fun p hp a ha =>
    conj_mem_unip_of_subset hcm hJ hW hTT'.1 hp ha
  obtain ⟨π, hπc, hπ, hπQ⟩ := GlobalTheory.T.restricted_automorphic_invariance D V m X Y hW T V' ι hι hr s hs _ _ hnorm hdec
  let s₁ : unip D.sp.cm.sig V'.gram X' {k} →* unip D.sp.cm.sig V.gram X (insert (e k) T) :=
    (s.comp (unip D.sp.cm.sig V'.gram X' {k}).subtype).codRestrict _ fun u => hs1 _ u.2
  have hs₁c : Continuous s₁ := (hsc.comp continuous_subtype_val).subtype_mk _
  have hπs : ∀ u, π (s₁ u) = u := fun u => (hπ _ _).2 (by
    change s u * (s u)⁻¹ ∈ _
    simp [one_mem])
  have hker : ∀ v, π v = 1 ↔ (v : GA D V) ∈ unip D.sp.cm.sig V.gram X T := fun v => by
    rw [hπ v 1]
    simp
  intro μ 𝓕 hμ h𝓕 h1 g
  have cN : GlobalTheory.Cusp.Cocompact (GQ V) (unip D.sp.cm.sig V.gram X (insert (e k) T)) := cocompact_unip_std hcm hJ hW _
  have key := GlobalTheory.Cusp.constTermOn_eq_integral_semidirect (GA D V) (GA D V') (GQ V) _ _ (GQ V') _ hle cN
    (cocompact_unip_std hcm hJ hW T) (cocompact_unip_std hcm hJ' hW' {k}) s₁ π hs₁c hπc hπs hker
    (fun u hu => hsQ _ hu) (fun v hv => hπQ v hv) ψ hψc
    (fun a ha y => hψl a (Subgroup.mem_sup_left ha) y)
    (fun γ hγ hγ' y => hψl γ (ratPts_unip_le_leftSub D V m X Y hW T _ hTT'.1 ⟨hγ, hγ'⟩) y) μ 𝓕 hμ h𝓕 h1 (s g * y)
  obtain ⟨μ₀, 𝓕₀, a1, a2, a3⟩ := exists_mass_one cN
  have hz := hψ0 μ₀ 𝓕₀ a1 a2 a3 (s g * y)
  have hct : GlobalTheory.Cusp.constTermOn (GQ V) (unip D.sp.cm.sig V.gram X (insert (e k) T)) ψ (s g * y) = 0 := by
    haveI := a1
    have e1 := GlobalTheory.Cusp.Stages.constTermOn_eq' (Γ := GQ V) (φ := ψ) (x := s g * y) a2 (fun γ hγ n => by
      simp only [Subgroup.coe_mul, mul_assoc]
      exact hψl _ (ratPts_unip_le_leftSub D V m X Y hW T _ hTT'.1 ⟨hγ, (γ : unip _ _ _ _).2⟩) _)
    rw [e1, ← hz]
    simp
  rw [hct] at key
  refine key.trans (MeasureTheory.integral_congr_ae (.of_forall fun u => ?_))
  change ψ (s u * (s g * y)) = ψ (s (u * g) * y)
  rw [map_mul, mul_assoc]

end GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.Slice
end
