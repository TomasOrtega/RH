import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.InertDef
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FinPartIdemMulMemIff

noncomputable section

namespace PositivityTheory.ThK

open scoped Matrix Pointwise
open NumberField IsDedekindDomain Topology GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.EmbChart (atPlace atPlace_mul_right evFin_atPlace)

/- English proof (translation)
Establish `e : IsClosedEmbedding (fun k : H => Units.embedProduct A k.1)` using `Units.isClosedEmbedding_embedProduct.comp hH.isClosedEmbedding_subtypeVal`. Establish `hc : IsCompact (S ×ˢ (MulOpposite.op '' S))` using `hS.prod (hS.image MulOpposite.continuous_op)`. Conclude with `(e.isCompact_preimage hc).of_isClosed_subset hK fun k hk => ⟨(h k hk).1, _, (h k hk).2, rfl⟩`.
-/
theorem isCompact_of_units {A : Type} [Monoid A] [TopologicalSpace A] [ContinuousMul A] [T2Space A]
    (H : Subgroup Aˣ) (hH : IsClosed (H : Set Aˣ)) (K : Set H) (hK : IsClosed K) (S : Set A) (hS : IsCompact S)
    (h : ∀ k ∈ K, (k.1 : A) ∈ S ∧ ((k⁻¹).1 : A) ∈ S) : IsCompact K := by
  have e : IsClosedEmbedding (fun k : H => Units.embedProduct A k.1) :=
    Units.isClosedEmbedding_embedProduct.comp hH.isClosedEmbedding_subtypeVal
  have hc : IsCompact (S ×ˢ (MulOpposite.op '' S)) := hS.prod (hS.image MulOpposite.continuous_op)
  exact (e.isCompact_preimage hc).of_isClosed_subset hK fun k hk => ⟨(h k hk).1, _, (h k hk).2, rfl⟩

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}

/- English proof (translation)
The claim follows from `IsModuleTopology.isTopologicalRing (AF F) _`.
-/
theorem kc_ring : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _

/- English proof (translation)
Use `haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F`. Take `⟨e⟩` from `GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) (AF F)`. Conclude with `e.isEmbedding.t2Space`.
-/
theorem adele_t2Space : T2Space (AE F E) := by
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  obtain ⟨e⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) (AF F)
  exact e.isEmbedding.t2Space

/- English proof (translation)
The claim follows from `IsModuleTopology.toContinuousSMul (AF F) _`.
-/
theorem kc_smul : ContinuousSMul (AF F) (AE F E) := IsModuleTopology.toContinuousSMul (AF F) _

attribute [local instance] kc_ring adele_t2Space kc_smul

/- English proof (translation)
The claim follows from `(continuous_const.prodMk (continuous_singleFin v) : Continuous fun a => ((0 : Ainf F), singleFin v a))`.
-/
theorem kc_cont_atPlace (v : Pl F) : Continuous (atPlace v) :=
  (continuous_const.prodMk (continuous_singleFin v) : Continuous fun a => ((0 : Ainf F), singleFin v a))

/- English proof (translation)
Introduce `u hu` and use `by rw [smul_eq_mul, mul_comm, atPlace_mul_right, hu, mul_zero, map_zero]`.
-/
theorem kc_at_atPlace (v : Pl F) (x : Fv F v) : At (evFin F v) (atPlace v x) := fun u hu => by
  rw [smul_eq_mul, mul_comm, atPlace_mul_right, hu, mul_zero, map_zero]

/- English proof (translation)
Establish `h1` using `hz (1 - atPlace v 1) (by rw [map_sub, map_one, evFin_atPlace, sub_self])`. Rewrite `h1` using `[sub_smul, one_smul, sub_eq_zero]`. Conclude with `h1.symm`.
-/
theorem kc_idem {M : Type} [AddCommGroup M] [Module (AF F) M] {v : Pl F} {z : M} (hz : At (evFin F v) z) :
    atPlace v 1 • z = z := by
  have h1 := hz (1 - atPlace v 1) (by rw [map_sub, map_one, evFin_atPlace, sub_self])
  rw [sub_smul, one_smul, sub_eq_zero] at h1
  exact h1.symm

/- English proof (translation)
Use `conv_lhs => rw [← kc_idem ha]`. Rewrite using `[smul_eq_mul, atPlace_mul_right, one_mul]`.
-/
theorem kc_eq_atPlace {v : Pl F} {a : AF F} (ha : At (evFin F v) a) : a = atPlace v (evFin F v a) := by
  conv_lhs => rw [← kc_idem ha]
  rw [smul_eq_mul, atPlace_mul_right, one_mul]

/- English proof (translation)
The claim follows from `AddSubgroup.subset_closure ⟨_, kc_at_atPlace v x, by rw [evFin_atPlace]; exact hx, y, hy, rfl⟩`.
-/
theorem kc_mem (W : Spc F E d) (v : Pl F) {x : Fv F v} (hx : x ∈ v.adicCompletionIntegers F) {y : Fin d → E}
    (hy : y ∈ W.L) : (fun i => atPlace v x • inclR (F := F) (AF F) (y i)) ∈ latW W v :=
  AddSubgroup.subset_closure ⟨_, kc_at_atPlace v x, by rw [evFin_atPlace]; exact hx, y, hy, rfl⟩

/- English proof (translation)
Establish `hZ : (W.L.restrictScalars ℤ).FG` using `hW.restrictScalars`. Take `⟨m, s, hs⟩` from `Submodule.fg_iff_exists_fin_generating_family.1 hZ`. Establish `hsL : ∀ j, s j ∈ W.L` using `fun j => by`. Establish `: s j ∈ W.L.restrictScalars ℤ` using `hs ▸ Submodule.subset_span ⟨j, rfl⟩`. Conclude with `this`.

Use `haveI := GlobalTheory.AdelicUnitaryTop.compactSpace_adicCompletionIntegers F v`. Set `f : (Fin m → v.adicCompletionIntegers F) →+ (Fin d → AE F E)` to `AddMonoidHom.mk' (fun a => ∑ j, fun i => atPlace v (a j : Fv F v) • inclR (F := F) (AF F) (s j i)) fun a b => by`. Rewrite using `[← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun j _ => funext fun i => ?_` and prove the remaining obligations. Establish `: ((a + b) j : Fv F v) = a j + b j` using `rfl`.

Rewrite using `[this, map_add, add_smul]`. Both sides reduce to the same expression. Establish `hf : Continuous f`. Express the relevant statement in the definitionally equal form `Continuous fun a : Fin m → v.adicCompletionIntegers F => ∑ j, fun i => atPlace v (a j : Fv F v) • inclR (F := F) (AF F) (s j i)`. Use `continuous_finsetSum _ fun j _ => continuous_pi fun i => ?_` and prove the remaining obligations.

Establish `h1 : Continuous fun a : Fin m → v.adicCompletionIntegers F => (a j : Fv F v)` using `Continuous.subtype_val (continuous_apply j)`. Establish `h2 : Continuous fun a : Fin m → v.adicCompletionIntegers F => atPlace v (a j : Fv F v)` using `(kc_cont_atPlace v).comp h1`. Conclude with `h2.fun_smul continuous_const`. Establish `e : latW W v = f.range`. Use `le_antisymm ((AddSubgroup.closure_le _).2 ?_) ?_` and prove the remaining obligations.

Introduce and unpack `_ ⟨a, ha, ha', y, hy, rfl⟩`. Establish `hy' : y ∈ Submodule.span ℤ (Set.range s)` using `by rw [hs]; exact hy`. Take `⟨c, rfl⟩` from `(Submodule.mem_span_range_iff_exists_fun ℤ).1 hy'`. Use `⟨fun j => c j • ⟨_, ha'⟩, funext fun i => ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(∑ j, fun i => atPlace v (c j • evFin F v a) • inclR (F := F) (AF F) (s j i)) i = _`.

Rewrite using `[Finset.sum_apply, Finset.sum_apply, map_sum, Finset.smul_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[map_zsmul, ← kc_eq_atPlace ha, Pi.smul_apply, map_zsmul, smul_assoc, smul_comm]`. Introduce and unpack `_ ⟨a, rfl⟩`. Express the relevant statement in the definitionally equal form `(∑ j, fun i => atPlace v (a j : Fv F v) • inclR (F := F) (AF F) (s j i)) ∈ latW W v`.

Conclude with `sum_mem fun j _ => kc_mem W v (a j).2 (hsL j)`. Rewrite using `[e, AddMonoidHom.coe_range]`. Conclude with `isCompact_range hf`.
-/
theorem isCompact_latW (W : Spc F E d) (hW : W.L.FG) (v : Pl F) : IsCompact (latW W v : Set (Fin d → AE F E)) := by
  have hZ : (W.L.restrictScalars ℤ).FG := hW.restrictScalars
  obtain ⟨m, s, hs⟩ := Submodule.fg_iff_exists_fin_generating_family.1 hZ
  have hsL : ∀ j, s j ∈ W.L := fun j => by
    have : s j ∈ W.L.restrictScalars ℤ := hs ▸ Submodule.subset_span ⟨j, rfl⟩
    exact this
  haveI := GlobalTheory.AdelicUnitaryTop.compactSpace_adicCompletionIntegers F v
  let f : (Fin m → v.adicCompletionIntegers F) →+ (Fin d → AE F E) :=
    AddMonoidHom.mk' (fun a => ∑ j, fun i => atPlace v (a j : Fv F v) • inclR (F := F) (AF F) (s j i)) fun a b => by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => funext fun i => ?_
      have : ((a + b) j : Fv F v) = a j + b j := rfl
      rw [this, map_add, add_smul]; rfl
  have hf : Continuous f := by
    change Continuous fun a : Fin m → v.adicCompletionIntegers F =>
      ∑ j, fun i => atPlace v (a j : Fv F v) • inclR (F := F) (AF F) (s j i)
    refine continuous_finsetSum _ fun j _ => continuous_pi fun i => ?_
    have h1 : Continuous fun a : Fin m → v.adicCompletionIntegers F => (a j : Fv F v) :=
      Continuous.subtype_val (continuous_apply j)
    have h2 : Continuous fun a : Fin m → v.adicCompletionIntegers F => atPlace v (a j : Fv F v) :=
      (kc_cont_atPlace v).comp h1
    exact h2.fun_smul continuous_const
  have e : latW W v = f.range := by
    refine le_antisymm ((AddSubgroup.closure_le _).2 ?_) ?_
    · rintro _ ⟨a, ha, ha', y, hy, rfl⟩
      have hy' : y ∈ Submodule.span ℤ (Set.range s) := by rw [hs]; exact hy
      obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).1 hy'
      refine ⟨fun j => c j • ⟨_, ha'⟩, funext fun i => ?_⟩
      change (∑ j, fun i => atPlace v (c j • evFin F v a) • inclR (F := F) (AF F) (s j i)) i = _
      rw [Finset.sum_apply, Finset.sum_apply, map_sum, Finset.smul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_zsmul, ← kc_eq_atPlace ha, Pi.smul_apply, map_zsmul, smul_assoc, smul_comm]
    · rintro _ ⟨a, rfl⟩
      change (∑ j, fun i => atPlace v (a j : Fv F v) • inclR (F := F) (AF F) (s j i)) ∈ latW W v
      exact sum_mem fun j _ => kc_mem W v (a j).2 (hsL j)
  rw [e, AddMonoidHom.coe_range]
  exact isCompact_range hf

/- English proof (translation)
Establish `hx : x ∈ Submodule.span E (W.L : Set (Fin d → E))`. Rewrite using `[Submodule.IsLattice.span_eq_top (A := E)]`. Discharge the goal by the elementary cases of `trivial`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem y hy => exact ⟨_, isCompact_latW W hW.fg v, fun M hM => hM _ (kc_mem W v (one_mem _) hy)⟩`.

Consider the case `zero`. Use `⟨{0}, isCompact_singleton, fun M _ => ?_⟩` and prove the remaining obligations. Establish `: (fun i => atPlace v 1 • inclR (F` using `F) (AF F) ((0 : Fin d → E) i)) = 0 := funext fun i => by`. Rewrite using `[Pi.zero_apply, map_zero, smul_zero]`. Both sides reduce to the same expression.

Rewrite using `[this, Matrix.mulVec_zero]`. Both sides reduce to the same expression. Consider the case `add y z _ _ hy hz`. Take `⟨C, hC, h⟩` from `hy`. Take `⟨C', hC', h'⟩` from `hz`.

Use `⟨C + C', hC.add hC', fun M hM => ?_⟩` and prove the remaining obligations. Establish `: (fun i => atPlace v 1 • inclR (F` using `F) (AF F) ((y + z) i)) = (fun i => atPlace v 1 • inclR (F := F) (AF F) (y i)) + fun i => atPlace v 1 • inclR (F := F) (AF F) (z i) :=`. Use function extensionality and compare the values at `fun i => by rw [Pi.add_apply, map_add, smul_add]; rfl`. Rewrite using `[this, Matrix.mulVec_add]`. Conclude with `Set.add_mem_add (h M hM) (h' M hM)`.

Consider the case `smul c y _ hy`. Take `⟨C, hC, h⟩` from `hy`. Use `⟨(fun z => inclR (F := F) (AF F) c • z) '' C, hC.image (continuous_const_smul _), fun M hM => ⟨_, h M hM, ?_⟩⟩` and prove the remaining obligations. Establish `: (fun i => atPlace v 1 • inclR (F` using `F) (AF F) ((c • y) i)) = inclR (F := F) (AF F) c • fun i => atPlace v 1 • inclR (F := F) (AF F) (y i) :=`. Use function extensionality and compare the values at `fun i => by rw [Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, map_mul, mul_smul_comm]`.

Rewrite using `[this, Matrix.mulVec_smul]`.
-/
theorem kc_bound (W : Spc F E d) (hW : W.L.IsLattice E) (v : Pl F) (x : Fin d → E) :
    ∃ C : Set (Fin d → AE F E), IsCompact C ∧ ∀ M : Matrix (Fin d) (Fin d) (AE F E),
      (∀ y ∈ latW W v, M *ᵥ y ∈ latW W v) → M *ᵥ (fun i => atPlace v 1 • inclR (F := F) (AF F) (x i)) ∈ C := by
  have hx : x ∈ Submodule.span E (W.L : Set (Fin d → E)) := by
    rw [Submodule.IsLattice.span_eq_top (A := E)]; trivial
  induction hx using Submodule.span_induction with
  | mem y hy => exact ⟨_, isCompact_latW W hW.fg v, fun M hM => hM _ (kc_mem W v (one_mem _) hy)⟩
  | zero =>
    refine ⟨{0}, isCompact_singleton, fun M _ => ?_⟩
    have : (fun i => atPlace v 1 • inclR (F := F) (AF F) ((0 : Fin d → E) i)) = 0 := funext fun i => by
      rw [Pi.zero_apply, map_zero, smul_zero]; rfl
    rw [this, Matrix.mulVec_zero]; rfl
  | add y z _ _ hy hz =>
    obtain ⟨C, hC, h⟩ := hy
    obtain ⟨C', hC', h'⟩ := hz
    refine ⟨C + C', hC.add hC', fun M hM => ?_⟩
    have : (fun i => atPlace v 1 • inclR (F := F) (AF F) ((y + z) i)) =
        (fun i => atPlace v 1 • inclR (F := F) (AF F) (y i)) + fun i => atPlace v 1 • inclR (F := F) (AF F) (z i) :=
      funext fun i => by rw [Pi.add_apply, map_add, smul_add]; rfl
    rw [this, Matrix.mulVec_add]
    exact Set.add_mem_add (h M hM) (h' M hM)
  | smul c y _ hy =>
    obtain ⟨C, hC, h⟩ := hy
    refine ⟨(fun z => inclR (F := F) (AF F) c • z) '' C, hC.image (continuous_const_smul _), fun M hM => ⟨_, h M hM, ?_⟩⟩
    have : (fun i => atPlace v 1 • inclR (F := F) (AF F) ((c • y) i)) =
        inclR (F := F) (AF F) c • fun i => atPlace v 1 • inclR (F := F) (AF F) (y i) :=
      funext fun i => by rw [Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, map_mul, mul_smul_comm]
    rw [this, Matrix.mulVec_smul]

/- English proof (translation)
Use `choose C hC h using fun j : Fin d => kc_bound W hW v (Pi.single j 1)`. Set `g : (Fin d → Fin d → AE F E) → Matrix (Fin d) (Fin d) (AE F E)` to `fun z => (Matrix.of z)ᵀ + (1 - atPlace v 1 • (1 : Matrix (Fin d) (Fin d) (AE F E)))`. Establish `hg : Continuous g` using `(Continuous.matrix_transpose (A := fun z => Matrix.of z) continuous_id).add continuous_const`. Use `⟨g '' Set.univ.pi C, (isCompact_univ_pi hC).image hg, fun M h1 hM => ⟨_, fun j _ => h j M hM, ?_⟩⟩` and prove the remaining obligations. Establish `e : (Matrix.of fun j => M *ᵥ fun i => atPlace v 1 • inclR (F` using `F) (AF F) ((Pi.single j 1 : Fin d → E) i))ᵀ = atPlace v 1 • M := by`.

Use extensionality with `i j`. Establish `: (fun i => atPlace v 1 • inclR (F` using `F) (AF F) ((Pi.single j 1 : Fin d → E) i)) = atPlace v 1 • (Pi.single j 1 : Fin d → AE F E) := funext fun k => by`. Distinguish the cases in `hk : k = j`. Substitute `hk` using the available equality. Simplify using the standard rewrite rules.

Simplify using `[hk]`. Rewrite using `[Matrix.transpose_apply, Matrix.of_apply, this, Matrix.mulVec_smul, Matrix.mulVec_single_one]`. Both sides reduce to the same expression. Establish `e1` using `kc_idem h1`. Express the relevant statement in the definitionally equal form `_ + _ = M`.

Rewrite using `[e]`. Rewrite `e1` using `[smul_sub]`. Rewrite using `[add_sub_left_comm, e1, add_sub_cancel]`.
-/
theorem kc_mat (W : Spc F E d) (hW : W.L.IsLattice E) (v : Pl F) :
    ∃ S : Set (Matrix (Fin d) (Fin d) (AE F E)), IsCompact S ∧ ∀ M : Matrix (Fin d) (Fin d) (AE F E),
      At (evFin F v) (M - 1) → (∀ y ∈ latW W v, M *ᵥ y ∈ latW W v) → M ∈ S := by
  choose C hC h using fun j : Fin d => kc_bound W hW v (Pi.single j 1)
  let g : (Fin d → Fin d → AE F E) → Matrix (Fin d) (Fin d) (AE F E) :=
    fun z => (Matrix.of z)ᵀ + (1 - atPlace v 1 • (1 : Matrix (Fin d) (Fin d) (AE F E)))
  have hg : Continuous g := (Continuous.matrix_transpose (A := fun z => Matrix.of z) continuous_id).add continuous_const
  refine ⟨g '' Set.univ.pi C, (isCompact_univ_pi hC).image hg, fun M h1 hM => ⟨_, fun j _ => h j M hM, ?_⟩⟩
  have e : (Matrix.of fun j => M *ᵥ fun i => atPlace v 1 • inclR (F := F) (AF F) ((Pi.single j 1 : Fin d → E) i))ᵀ =
      atPlace v 1 • M := by
    ext i j
    have : (fun i => atPlace v 1 • inclR (F := F) (AF F) ((Pi.single j 1 : Fin d → E) i)) =
        atPlace v 1 • (Pi.single j 1 : Fin d → AE F E) := funext fun k => by
      by_cases hk : k = j
      · subst hk; simp
      · simp [hk]
    rw [Matrix.transpose_apply, Matrix.of_apply, this, Matrix.mulVec_smul, Matrix.mulVec_single_one]
    rfl
  have e1 := kc_idem h1
  change _ + _ = M
  rw [e]
  rw [smul_sub] at e1
  rw [add_sub_left_comm, e1, add_sub_cancel]

/- English proof (translation)
Establish `hc : Continuous (cA (F` using `F) σ) := IsModuleTopology.continuous_of_linearMap (cA (F := F) σ).toLinearMap`. Conclude with `isClosed_eq (((Units.continuous_val.matrix_transpose).matrix_mul continuous_const).matrix_mul (Units.continuous_val.matrix_map hc)) continuous_const`.
-/
theorem kc_closedU (J : Matrix (Fin d) (Fin d) E) :
    IsClosed ((UG (cA σ) (incM F J) : Subgroup (GL (Fin d) (AE F E))) : Set (GL (Fin d) (AE F E))) := by
  have hc : Continuous (cA (F := F) σ) := IsModuleTopology.continuous_of_linearMap (cA (F := F) σ).toLinearMap
  exact isClosed_eq (((Units.continuous_val.matrix_transpose).matrix_mul continuous_const).matrix_mul
    (Units.continuous_val.matrix_map hc)) continuous_const

/- English proof (translation)
The claim follows from `Units.continuous_val.comp continuous_subtype_val`.
-/
theorem kc_cont_mat (J : Matrix (Fin d) (Fin d) E) : Continuous (mat : UA σ J → _) :=
  Units.continuous_val.comp continuous_subtype_val

/- English proof (translation)
Take `⟨S, hS, h⟩` from `kc_mat W hW v`. Establish `hL` using `(isCompact_latW W hW.fg v).isClosed`. Establish `hm` using `kc_cont_mat (σ := σ) W.J`. Establish `hi : Continuous fun k : UA σ W.J => mat k⁻¹` using `hm.comp continuous_inv`. Use `isCompact_of_units _ (kc_closedU W.J) _ ?_ S hS fun k hk => ⟨h _ hk.1 fun y hy => (hk.2 y hy).1, h _ (fun u hu => ?_) fun y hy => (hk.2 y hy).2⟩` and prove the remaining obligations.

Establish `e : KAt σ W v = (⋂ u, ⋂ _ : evFin F v u = 0, {k : UA σ W.J | u • (mat k - 1) = 0}) ∩ ⋂ y, ⋂ _ : y ∈ latW W v, ((fun k : UA σ W.J => mat k *ᵥ y) ⁻¹' latW W v ∩ (fun k : UA σ W.J => mat k⁻¹ *ᵥ y) ⁻¹' latW W v)`. Use extensionality with `k`. Simplify using `only [Set.mem_inter_iff, Set.mem_iInter]`. Both sides reduce to the same expression. Rewrite using `[e]`.

Use `IsClosed.inter (isClosed_iInter fun u => isClosed_iInter fun _ => isClosed_eq ((hm.sub continuous_const).const_smul u) continuous_const) (isClosed_iInter fun y => isClosed_iInter fun _ => IsClosed.inter (hL.preimage (hm.matrix_mulVec continuous_const)) (hL.preimage (hi.matrix_mul …` and prove the remaining obligations. Establish `e0 : mat k⁻¹ * mat k = 1`. Establish `: mat (k⁻¹ * k) = mat k⁻¹ * mat k` using `rfl`. Rewrite using `[← this, inv_mul_cancel]`. Both sides reduce to the same expression.

Establish `e : mat k⁻¹ - 1 = -(mat k⁻¹ * (mat k - 1))` using `by rw [mul_sub, e0, mul_one, neg_sub]`. Express the relevant statement in the definitionally equal form `u • (mat k⁻¹ - 1) = 0`. Rewrite using `[e, smul_neg, ← Matrix.mul_smul, hk.1 u hu, Matrix.mul_zero, neg_zero]`.
-/
theorem isCompact_KAt (W : Spc F E d) (hW : W.L.IsLattice E) (v : Pl F) : IsCompact (KAt σ W v) := by
  obtain ⟨S, hS, h⟩ := kc_mat W hW v
  have hL := (isCompact_latW W hW.fg v).isClosed
  have hm := kc_cont_mat (σ := σ) W.J
  have hi : Continuous fun k : UA σ W.J => mat k⁻¹ := hm.comp continuous_inv
  refine isCompact_of_units _ (kc_closedU W.J) _ ?_ S hS fun k hk =>
    ⟨h _ hk.1 fun y hy => (hk.2 y hy).1, h _ (fun u hu => ?_) fun y hy => (hk.2 y hy).2⟩
  · have e : KAt σ W v = (⋂ u, ⋂ _ : evFin F v u = 0, {k : UA σ W.J | u • (mat k - 1) = 0}) ∩
        ⋂ y, ⋂ _ : y ∈ latW W v, ((fun k : UA σ W.J => mat k *ᵥ y) ⁻¹' latW W v ∩
          (fun k : UA σ W.J => mat k⁻¹ *ᵥ y) ⁻¹' latW W v) := by
      ext k
      simp only [Set.mem_inter_iff, Set.mem_iInter]
      rfl
    rw [e]
    refine IsClosed.inter (isClosed_iInter fun u => isClosed_iInter fun _ =>
      isClosed_eq ((hm.sub continuous_const).const_smul u) continuous_const)
      (isClosed_iInter fun y => isClosed_iInter fun _ => IsClosed.inter
        (hL.preimage (hm.matrix_mulVec continuous_const)) (hL.preimage (hi.matrix_mulVec continuous_const)))
  · have e0 : mat k⁻¹ * mat k = 1 := by
      have : mat (k⁻¹ * k) = mat k⁻¹ * mat k := rfl
      rw [← this, inv_mul_cancel]; rfl
    have e : mat k⁻¹ - 1 = -(mat k⁻¹ * (mat k - 1)) := by rw [mul_sub, e0, mul_one, neg_sub]
    change u • (mat k⁻¹ - 1) = 0
    rw [e, smul_neg, ← Matrix.mul_smul, hk.1 u hu, Matrix.mul_zero, neg_zero]

/- English proof (translation)
Introduce `_ _ _ _ _ _ _ _ _ _ _ _ W _ _ h v` and use `let ⟨_, _, hW⟩ := h.skew isCompact_KAt W hW.lat v`.
-/
theorem stabiliser_compact : KCompact := fun _ _ _ _ _ _ _ _ _ _ _ _ W _ _ h v =>
  let ⟨_, _, hW⟩ := h.skew
  isCompact_KAt W hW.lat v

end PositivityTheory.ThK
