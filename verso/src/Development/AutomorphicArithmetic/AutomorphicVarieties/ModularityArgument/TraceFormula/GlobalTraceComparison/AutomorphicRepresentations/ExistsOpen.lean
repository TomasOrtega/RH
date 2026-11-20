import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.SlotBasic
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.FinprodSplitAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.UnitHecke
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLocCompAndIsLocLoc

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host Matrix GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.BCT
open UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi UpperTheory.Zero.ConvolutionTheory.EB PositivityTheory.Rg.BcB.Desc

namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.IsotypicAlt

section Abs

variable {G W V : Type} [Group G] [AddCommGroup W] [Module ℂ W] [AddCommGroup V] [Module ℂ V]

/- English proof (translation)
Introduce `h`. Take `⟨x, hx⟩` from `exists_ne (0 : V)`. Establish `h1 : ρ g (ρ g⁻¹ x) = x`. Rewrite using `[← Module.End.mul_apply, ← map_mul]`. Simplify using the standard rewrite rules.

Conclude with `hx (by rw [← h1, h]; simp)`.
-/
private theorem rep_ne [Nontrivial V] (ρ : Representation ℂ G V) (g : G) : ρ g ≠ 0 := by
  intro h
  obtain ⟨x, hx⟩ := exists_ne (0 : V)
  have h1 : ρ g (ρ g⁻¹ x) = x := by
    rw [← Module.End.mul_apply, ← map_mul]
    simp
  exact hx (by rw [← h1, h]; simp)

/- English proof (translation)
Use extensionality with `q`. Use `rep_ne ρ q.out` as an intermediate fact. Simplify using `only [Function.mem_support, LinearMap.comp_id, ne_eq, smul_eq_zero, this, or_false]`.
-/
private theorem supp_eq [Nontrivial V] (ρ : Representation ℂ G V) (K : Subgroup G) (f : G → ℂ) :
    Function.support (fun q : G ⧸ K => f q.out • (ρ q.out ∘ₗ (LinearMap.id : V →ₗ[ℂ] V))) =
      Function.support fun q : G ⧸ K => f q.out := by
  ext q
  have := rep_ne ρ q.out
  simp only [Function.mem_support, LinearMap.comp_id, ne_eq, smul_eq_zero, this, or_false]

/- English proof (translation)
Unfold `Lv GlobalTheory.BCT.levOp`. Simplify using `only [LinearMap.smul_apply, map_smul]`. Use `congr 1`. Distinguish the cases in `hfin : (Function.support fun q : G ⧸ K => f q.out).Finite`. Rewrite using `[finsum_eq_sum_of_support_subset (s := hfin.toFinset) _ (by rw [supp_eq]; simp), finsum_eq_sum_of_support_subset (s := hfin.toFinset) _ (by rw [supp_eq]; simp)]`.

Simplify using `[LinearMap.sum_apply, map_sum, hT]`. Rewrite using `[finsum_of_infinite_support (by rwa [supp_eq]), finsum_of_infinite_support (by rwa [supp_eq])]`. Simplify using the standard rewrite rules.
-/
private theorem lv_inter [Nontrivial W] [Nontrivial V] (σ : Representation ℂ G W) (ρ : Representation ℂ G V)
    (T : W →ₗ[ℂ] V) (hT : ∀ g v, T (σ g v) = ρ g (T v)) (K : Subgroup G) (f : G → ℂ) (x : W) :
    T (Lv σ K f x) = Lv ρ K f (T x) := by
  unfold Lv GlobalTheory.BCT.levOp
  simp only [LinearMap.smul_apply, map_smul]
  congr 1
  by_cases hfin : (Function.support fun q : G ⧸ K => f q.out).Finite
  · rw [finsum_eq_sum_of_support_subset (s := hfin.toFinset) _ (by rw [supp_eq]; simp),
      finsum_eq_sum_of_support_subset (s := hfin.toFinset) _ (by rw [supp_eq]; simp)]
    simp [LinearMap.sum_apply, map_sum, hT]
  · rw [finsum_of_infinite_support (by rwa [supp_eq]), finsum_of_infinite_support (by rwa [supp_eq])]
    simp

/- English proof (translation)
Proceed by induction on `p using FreeAlgebra.induction with`. Consider the case `grade0 r => intro x`. Simplify using `[Algebra.algebraMap_eq_smul_one]`. Consider the case `grade1 f => intro x`. Simplify using `[lv_inter σ ρ T hT]`.

Consider the case `mul a b ha hb => intro x`. Simplify using `[map_mul, Module.End.mul_apply, ha, hb]`. Consider the case `add a b ha hb => intro x`. Simplify using `[map_add, LinearMap.add_apply, ha, hb]`.
-/
private theorem lift_inter [Nontrivial W] [Nontrivial V] (σ : Representation ℂ G W) (ρ : Representation ℂ G V)
    (T : W →ₗ[ℂ] V) (hT : ∀ g v, T (σ g v) = ρ g (T v)) (K : Subgroup G) (p : FreeAlgebra ℂ (G → ℂ)) :
    ∀ x : W, T (FreeAlgebra.lift ℂ (Lv σ K) p x) = FreeAlgebra.lift ℂ (Lv ρ K) p (T x) := by
  induction p using FreeAlgebra.induction with
  | grade0 r => intro x; simp [Algebra.algebraMap_eq_smul_one]
  | grade1 f => intro x; simp [lv_inter σ ρ T hT]
  | mul a b ha hb => intro x; simp [map_mul, Module.End.mul_apply, ha, hb]
  | add a b ha hb => intro x; simp [map_add, LinearMap.add_apply, ha, hb]

private def isoM (σ : Representation ℂ G W) (ρ : Representation ℂ G V) (H : Subgroup G) : Submodule ℂ V :=
  ⨆ f : {f : W →ₗ[ℂ] V // ∀ g v, f (σ g v) = ρ g (f v)}, (fixed σ H).map f.1

/- English proof (translation)
The claim follows from `iSup_mono fun _ => Submodule.map_mono fun _ hx => LocEx.mem_fix.2 fun k hk => LocEx.mem_fix.1 hx k (h hk)`.
-/
private theorem isoM_mono (σ : Representation ℂ G W) (ρ : Representation ℂ G V) {H H' : Subgroup G} (h : H' ≤ H) :
    isoM σ ρ H ≤ isoM σ ρ H' :=
  iSup_mono fun _ => Submodule.map_mono fun _ hx => LocEx.mem_fix.2 fun k hk => LocEx.mem_fix.1 hx k (h hk)

/- English proof (translation)
Proceed by induction on `hy using Submodule.iSup_induction' with`. Consider the case `mem f y hy`. Take `⟨v, rfl⟩` from `hy`. Use `⟨LocEx.stab σ v, hσ v, Submodule.mem_iSup_of_mem f ⟨v, LocEx.mem_fix.2 fun k hk => hk, rfl⟩⟩` and prove the remaining obligations. Consider the case `zero => exact ⟨⊤, isOpen_univ, zero_mem _⟩`.

Consider the case `add a b _ _ ha hb`. Take `⟨H, hH, ha⟩` from `ha`. Take `⟨H', hH', hb⟩` from `hb`. Conclude with `⟨H ⊓ H', hH.inter hH', add_mem (isoM_mono σ ρ inf_le_left ha) (isoM_mono σ ρ inf_le_right hb)⟩`.
-/
private theorem exists_open [TopologicalSpace G] [IsTopologicalGroup G] (σ : Representation ℂ G W)
    (ρ : Representation ℂ G V) (hσ : IsSmooth σ) {y : V}
    (hy : y ∈ ⨆ f : {f : W →ₗ[ℂ] V // ∀ g v, f (σ g v) = ρ g (f v)}, LinearMap.range f.1) :
    ∃ H : Subgroup G, IsOpen (H : Set G) ∧ y ∈ isoM σ ρ H := by
  induction hy using Submodule.iSup_induction' with
  | mem f y hy =>
    obtain ⟨v, rfl⟩ := hy
    refine ⟨LocEx.stab σ v, hσ v, Submodule.mem_iSup_of_mem f ⟨v, LocEx.mem_fix.2 fun k hk => hk, rfl⟩⟩
  | zero => exact ⟨⊤, isOpen_univ, zero_mem _⟩
  | add a b _ _ ha hb =>
    obtain ⟨H, hH, ha⟩ := ha
    obtain ⟨H', hH', hb⟩ := hb
    exact ⟨H ⊓ H', hH.inter hH', add_mem (isoM_mono σ ρ inf_le_left ha) (isoM_mono σ ρ inf_le_right hb)⟩

/- English proof (translation)
Take `⟨h, hh⟩` from `QuotientGroup.mk_out_eq_mul (H.subgroupOf N) c`. Rewrite using `[hh]`. Establish `h1 : ((h : N) : G) ∈ H` using `Subgroup.mem_subgroupOf.1 h.2`. Simplify using `only [Subgroup.coe_mul, map_mul, Module.End.mul_apply, LocEx.mem_fix.1 hx _ h1]`.
-/
private theorem out_act (σ : Representation ℂ G W) (N H : Subgroup G) {x : W} (hx : x ∈ fixed σ H) (c : N) :
    σ ((QuotientGroup.mk c : N ⧸ H.subgroupOf N).out : N).1 x = σ c.1 x := by
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul (H.subgroupOf N) c
  rw [hh]
  have h1 : ((h : N) : G) ∈ H := Subgroup.mem_subgroupOf.1 h.2
  simp only [Subgroup.coe_mul, map_mul, Module.End.mul_apply, LocEx.mem_fix.1 hx _ h1]

private def cs {U : Type} [AddCommGroup U] [Module ℂ U] (r : Representation ℂ G U) (N H : Subgroup G)
    [Fintype (N ⧸ H.subgroupOf N)] : Module.End ℂ U :=
  ∑ q : N ⧸ H.subgroupOf N, r (q.out : N).1

/- English proof (translation)
Use `LocEx.mem_fix.2 fun n hn => ?_` and prove the remaining obligations. Establish `key : ∀ q : N ⧸ H.subgroupOf N, σ n (σ (q.out : N).1 x) = σ (((⟨n, hn⟩ : N) • q).out : N).1 x` using `fun q => by`. Establish `e : ((⟨n, hn⟩ : N) • q) = QuotientGroup.mk ((⟨n, hn⟩ : N) * q.out)` using `by conv_lhs => rw [← QuotientGroup.out_eq' q]`. Both sides reduce to the same expression. Rewrite using `[e, out_act σ N H hx]`.

Simplify using `only [Subgroup.coe_mul, map_mul, Module.End.mul_apply]`. Simplify using `only [cs, LinearMap.sum_apply, map_sum, key]`. Conclude with `Equiv.sum_comp (MulAction.toPerm (⟨n, hn⟩ : N)) fun q : N ⧸ H.subgroupOf N => σ (q.out : N).1 x`.
-/
private theorem cs_fixed (σ : Representation ℂ G W) (N H : Subgroup G) [Fintype (N ⧸ H.subgroupOf N)] {x : W}
    (hx : x ∈ fixed σ H) : cs σ N H x ∈ fixed σ N := by
  refine LocEx.mem_fix.2 fun n hn => ?_
  have key : ∀ q : N ⧸ H.subgroupOf N, σ n (σ (q.out : N).1 x) =
      σ (((⟨n, hn⟩ : N) • q).out : N).1 x := fun q => by
    have e : ((⟨n, hn⟩ : N) • q) = QuotientGroup.mk ((⟨n, hn⟩ : N) * q.out) := by
      conv_lhs => rw [← QuotientGroup.out_eq' q]
      rfl
    rw [e, out_act σ N H hx]
    simp only [Subgroup.coe_mul, map_mul, Module.End.mul_apply]
  simp only [cs, LinearMap.sum_apply, map_sum, key]
  exact Equiv.sum_comp (MulAction.toPerm (⟨n, hn⟩ : N)) fun q : N ⧸ H.subgroupOf N => σ (q.out : N).1 x

/- English proof (translation)
Establish `h1 : cs ρ N H y ∈ isoM σ ρ N`. Use `Submodule.mem_comap.1 ((iSup_le fun f => ?_ : isoM σ ρ H ≤ (isoM σ ρ N).comap (cs ρ N H)) hy)` and prove the remaining obligations. Introduce and unpack `_ ⟨x, hx, rfl⟩`. Use `Submodule.mem_iSup_of_mem f ⟨cs σ N H x, cs_fixed σ N H hx, ?_⟩` and prove the remaining obligations. Simplify using `only [cs, LinearMap.sum_apply, map_sum, f.2]`.

Establish `h2 : cs ρ N H y = (Fintype.card (N ⧸ H.subgroupOf N) : ℂ) • y`. Simplify using `only [cs, LinearMap.sum_apply]`. Rewrite using `[Finset.sum_congr rfl fun q _ => LocEx.mem_fix.1 hf _ (q.out : N).2]`. Simplify using `[Nat.cast_smul_eq_nsmul]`. Establish `h3 : (Fintype.card (N ⧸ H.subgroupOf N) : ℂ) ≠ 0` using `by haveI : Nonempty (N ⧸ H.subgroupOf N) := ⟨QuotientGroup.mk 1⟩`.

Conclude with `Nat.cast_ne_zero.2 Fintype.card_ne_zero`. Rewrite `h1` using `[h2]`. Conclude with `(Submodule.smul_mem_iff _ h3).1 h1`.
-/
private theorem avg_mem (σ : Representation ℂ G W) (ρ : Representation ℂ G V) (N H : Subgroup G)
    [Fintype (N ⧸ H.subgroupOf N)] {y : V} (hy : y ∈ isoM σ ρ H) (hf : y ∈ fixed ρ N) : y ∈ isoM σ ρ N := by
  have h1 : cs ρ N H y ∈ isoM σ ρ N := by
    refine Submodule.mem_comap.1 ((iSup_le fun f => ?_ : isoM σ ρ H ≤ (isoM σ ρ N).comap (cs ρ N H)) hy)
    rintro _ ⟨x, hx, rfl⟩
    refine Submodule.mem_iSup_of_mem f ⟨cs σ N H x, cs_fixed σ N H hx, ?_⟩
    simp only [cs, LinearMap.sum_apply, map_sum, f.2]
  have h2 : cs ρ N H y = (Fintype.card (N ⧸ H.subgroupOf N) : ℂ) • y := by
    simp only [cs, LinearMap.sum_apply]
    rw [Finset.sum_congr rfl fun q _ => LocEx.mem_fix.1 hf _ (q.out : N).2]
    simp [Nat.cast_smul_eq_nsmul]
  have h3 : (Fintype.card (N ⧸ H.subgroupOf N) : ℂ) ≠ 0 := by
    haveI : Nonempty (N ⧸ H.subgroupOf N) := ⟨QuotientGroup.mk 1⟩
    exact Nat.cast_ne_zero.2 Fintype.card_ne_zero
  rw [h2] at h1
  exact (Submodule.smul_mem_iff _ h3).1 h1

/- English proof (translation)
Take `⟨H, hH, hyH⟩` from `exists_open σ ρ hσ (hI ▸ Submodule.mem_top : y ∈ _)`. Use `haveI : CompactSpace N := isCompact_iff_compactSpace.1 hNc`. Use `haveI : Finite (N ⧸ H.subgroupOf N) := Subgroup.quotient_finite_of_isOpen _ (hH.preimage continuous_subtype_val)`. Use `haveI := Fintype.ofFinite (N ⧸ H.subgroupOf N)`. Establish `hyN` using `avg_mem σ ρ N H hyH hy`.

Use `Submodule.mem_comap.1 ((iSup_le fun f => ?_ : isoM σ ρ N ≤ (⊥ : Submodule ℂ V).comap (FreeAlgebra.lift ℂ (Lv ρ N) p)) hyN)` and prove the remaining obligations. Introduce and unpack `_ ⟨x, hx, rfl⟩`. Rewrite using `[Submodule.mem_comap, Submodule.mem_bot, ← lift_inter σ ρ f.1 f.2 N p x, hp x hx, map_zero]`.
-/
private theorem iso_abs [TopologicalSpace G] [IsTopologicalGroup G] [Nontrivial W] [Nontrivial V]
    (σ : Representation ℂ G W) (ρ : Representation ℂ G V) (hσ : IsSmooth σ) (N : Subgroup G)
    (hNc : IsCompact (N : Set G))
    (hI : ⨆ f : {f : W →ₗ[ℂ] V // ∀ g v, f (σ g v) = ρ g (f v)}, LinearMap.range f.1 = ⊤)
    (p : FreeAlgebra ℂ (G → ℂ)) (hp : ∀ x ∈ fixed σ N, FreeAlgebra.lift ℂ (Lv σ N) p x = 0)
    (y : V) (hy : y ∈ fixed ρ N) : FreeAlgebra.lift ℂ (Lv ρ N) p y = 0 := by
  obtain ⟨H, hH, hyH⟩ := exists_open σ ρ hσ (hI ▸ Submodule.mem_top : y ∈ _)
  haveI : CompactSpace N := isCompact_iff_compactSpace.1 hNc
  haveI : Finite (N ⧸ H.subgroupOf N) :=
    Subgroup.quotient_finite_of_isOpen _ (hH.preimage continuous_subtype_val)
  haveI := Fintype.ofFinite (N ⧸ H.subgroupOf N)
  have hyN := avg_mem σ ρ N H hyH hy
  refine Submodule.mem_comap.1 ((iSup_le fun f => ?_ :
    isoM σ ρ N ≤ (⊥ : Submodule ℂ V).comap (FreeAlgebra.lift ℂ (Lv ρ N) p)) hyN)
  rintro _ ⟨x, hx, rfl⟩
  rw [Submodule.mem_comap, Submodule.mem_bot, ← lift_inter σ ρ f.1 f.2 N p x, hp x hx, map_zero]

end Abs

section Conc

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

/- English proof (translation)
Use `set M : Submodule ℂ π.V := ⨆ f : {f : τ.V →ₗ[ℂ] π.V // ∀ g v, f (τ.ρ g v) = π.locRep w g (f v)}, LinearMap.range f.1 with hM`. Establish `comm : ∀ T : Module.End ℂ π.V, (∀ g x, T (π.locRep w g x) = π.locRep w g (T x)) → ∀ x ∈ M, T x ∈ M`. Introduce `T hT x hx`. Use `Submodule.mem_comap.1 ((iSup_le fun f => ?_ : M ≤ M.comap T) hx)` and prove the remaining obligations. Introduce and unpack `_ ⟨v, rfl⟩`.

Conclude with `Submodule.mem_iSup_of_mem ⟨T ∘ₗ f.1, fun g v => by`. Rewrite using `[LinearMap.comp_apply, f.2, hT]`. Use the proof step `rfl⟩ ⟨v, rfl⟩`. Establish `loc : ∀ g, ∀ x ∈ M, π.locRep w g x ∈ M`. Introduce `g x hx`.

Use `Submodule.mem_comap.1 ((iSup_le fun f => ?_ : M ≤ M.comap (π.locRep w g)) hx)` and prove the remaining obligations. Introduce and unpack `_ ⟨v, rfl⟩`. Conclude with `Submodule.mem_iSup_of_mem f ⟨τ.ρ g v, f.2 g v⟩`. Establish `hop : ∀ (o : Op E n), ∀ x ∈ M, π.op o x ∈ M`. Introduce `o x hx`.

Consider the cases of `o with`. Consider the case `fin k => set c := GeneralLinearGroup.map (pLoc E w) k`. Establish `h1` using `loc c _ (comm (π.finPart ((locGL E n w c)⁻¹ * k)) (fun g y => by`. Simplify using `only [CuspSub.locRep, MonoidHom.comp_apply]`. Rewrite using `[← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, LocUniq.comm_locGL w (LocEx.map_pLoc_inv_mul w k)]) x hx)`.

Establish `e : π.locRep w c (π.finPart ((locGL E n w c)⁻¹ * k) x) = π.op (.fin k) x`. Rewrite using `[CuspSub.locRep, MonoidHom.comp_apply, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left]`. Both sides reduce to the same expression. Rewrite `h1` using `[e]`. Then use the resulting hypothesis. Consider the case `cpt k`.

Use `comm _ (fun g y => Subtype.ext ?_) x hx` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(rt E n (infGL E n (Unitary.toUnits k)) * rt E n (finGL E n (locGL E n w g))) y.1 = (rt E n (finGL E n (locGL E n w g)) * rt E n (infGL E n (Unitary.toUnits k))) y.1`. Rewrite using `[← map_mul, ← map_mul, infGL_comm]`. Consider the case `lie X`. Conclude with `comm _ (fun g y => Subtype.ext (LinearMap.congr_fun (lie_rt_fin X (locGL E n w g)) y.1)) x hx`.

Establish `hi` using `Submodule.map_injective_of_injective π.V.injective_subtype`. Break down `π.irred (M.map π.V.subtype) (Submodule.map_subtype_le _ _) (by` into its components or cases. Introduce and unpack `o _ ⟨x, hx, rfl⟩`. Conclude with `⟨_, hop o x hx, rfl⟩) with h | h`. Take `⟨f, f0, hf⟩` from `hτ`.

Establish `hb : M = ⊥` using `hi (h.trans (Submodule.map_bot _).symm)`. Use `absurd (LinearMap.range_eq_bot.1 (le_bot_iff.1 ?_)) f0` and prove the remaining obligations. Rewrite using `[← hb]`. Conclude with `le_iSup (fun f : {f : τ.V →ₗ[ℂ] π.V // ∀ g v, f (τ.ρ g v) = π.locRep w g (f v)} => LinearMap.range f.1) ⟨f, hf⟩`. Conclude with `hi (h.trans (Submodule.map_subtype_top _).symm)`.
-/
private theorem iso_top (π : CuspSub E n) (w : HeightOneSpectrum (𝓞 E)) (τ : SmIrr (GL (Fin n) (w.adicCompletion E)))
    (hτ : π.IsLocComp w τ) :
    ⨆ f : {f : τ.V →ₗ[ℂ] π.V // ∀ g v, f (τ.ρ g v) = π.locRep w g (f v)}, LinearMap.range f.1 = ⊤ := by
  set M : Submodule ℂ π.V :=
    ⨆ f : {f : τ.V →ₗ[ℂ] π.V // ∀ g v, f (τ.ρ g v) = π.locRep w g (f v)}, LinearMap.range f.1 with hM
  have comm : ∀ T : Module.End ℂ π.V, (∀ g x, T (π.locRep w g x) = π.locRep w g (T x)) → ∀ x ∈ M, T x ∈ M := by
    intro T hT x hx
    refine Submodule.mem_comap.1 ((iSup_le fun f => ?_ : M ≤ M.comap T) hx)
    rintro _ ⟨v, rfl⟩
    exact Submodule.mem_iSup_of_mem ⟨T ∘ₗ f.1, fun g v => by
      rw [LinearMap.comp_apply, f.2, hT]; rfl⟩ ⟨v, rfl⟩
  have loc : ∀ g, ∀ x ∈ M, π.locRep w g x ∈ M := by
    intro g x hx
    refine Submodule.mem_comap.1 ((iSup_le fun f => ?_ : M ≤ M.comap (π.locRep w g)) hx)
    rintro _ ⟨v, rfl⟩
    exact Submodule.mem_iSup_of_mem f ⟨τ.ρ g v, f.2 g v⟩
  have hop : ∀ (o : Op E n), ∀ x ∈ M, π.op o x ∈ M := by
    intro o x hx
    cases o with
    | fin k =>
      set c := GeneralLinearGroup.map (pLoc E w) k
      have h1 := loc c _ (comm (π.finPart ((locGL E n w c)⁻¹ * k)) (fun g y => by
        simp only [CuspSub.locRep, MonoidHom.comp_apply]
        rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul,
          LocUniq.comm_locGL w (LocEx.map_pLoc_inv_mul w k)]) x hx)
      have e : π.locRep w c (π.finPart ((locGL E n w c)⁻¹ * k) x) = π.op (.fin k) x := by
        rw [CuspSub.locRep, MonoidHom.comp_apply, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left]
        rfl
      rwa [e] at h1
    | cpt k =>
      refine comm _ (fun g y => Subtype.ext ?_) x hx
      change (rt E n (infGL E n (Unitary.toUnits k)) * rt E n (finGL E n (locGL E n w g))) y.1 =
        (rt E n (finGL E n (locGL E n w g)) * rt E n (infGL E n (Unitary.toUnits k))) y.1
      rw [← map_mul, ← map_mul, infGL_comm]
    | lie X =>
      exact comm _ (fun g y => Subtype.ext (LinearMap.congr_fun (lie_rt_fin X (locGL E n w g)) y.1)) x hx
  have hi := Submodule.map_injective_of_injective π.V.injective_subtype
  rcases π.irred (M.map π.V.subtype) (Submodule.map_subtype_le _ _) (by
    rintro o _ ⟨x, hx, rfl⟩
    exact ⟨_, hop o x hx, rfl⟩) with h | h
  · obtain ⟨f, f0, hf⟩ := hτ
    have hb : M = ⊥ := hi (h.trans (Submodule.map_bot _).symm)
    refine absurd (LinearMap.range_eq_bot.1 (le_bot_iff.1 ?_)) f0
    rw [← hb]
    exact le_iSup (fun f : {f : τ.V →ₗ[ℂ] π.V // ∀ g v, f (τ.ρ g v) = π.locRep w g (f v)} => LinearMap.range f.1) ⟨f, hf⟩
  · exact hi (h.trans (Submodule.map_subtype_top _).symm)

end Conc

end UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.IsotypicAlt

open UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.IsotypicAlt in
/- English proof (translation)
Introduce `_ E _ _ _ n π w τ hτ N hNo hNK p hp y hyπ hy`. Establish `hNc : IsCompact (N : Set (GLw n w))` using `(Asm.unitHecke E n 0 0 w).2.2.2.1.of_isClosed_subset (Subgroup.isClosed_of_isOpen N hNo) hNK`. Take `⟨f, f0, hf⟩` from `id hτ`. Use `haveI : Nontrivial τ.V := by`. Assume the negation of the conclusion as `h`.

Rewrite `h` using `[not_nontrivial_iff_subsingleton]`. Conclude with `f0 (LinearMap.ext fun v => by rw [Subsingleton.elim v 0]; simp)`. Use `haveI : Nontrivial π.V := Submodule.nontrivial_iff_ne_bot.2 π.ne_bot`. Use `haveI : Nontrivial (Sm E n) := π.V.injective_subtype.nontrivial`. Establish `hy' : (⟨y, hyπ⟩ : π.V) ∈ fixed (π.locRep w) N` using `LocEx.mem_fix.2 fun k hk => Subtype.ext (LocEx.mem_fix.1 hy k hk)`.

Establish `h1` using `iso_abs τ.ρ (π.locRep w) τ.smooth N hNc (iso_top π w τ hτ) p hp _ hy'`. Establish `h2` using `lift_inter (π.locRep w) (rw' n w false) π.V.subtype (fun _ _ => rfl) N p ⟨y, hyπ⟩`. Rewrite `h2` using `[h1, map_zero]`. Conclude with `h2.symm`.
-/
theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.isot_pf :
    SlotBasic → Isot := by
  intro _ E _ _ _ n π w τ hτ N hNo hNK p hp y hyπ hy
  have hNc : IsCompact (N : Set (GLw n w)) :=
    (Asm.unitHecke E n 0 0 w).2.2.2.1.of_isClosed_subset (Subgroup.isClosed_of_isOpen N hNo) hNK
  obtain ⟨f, f0, hf⟩ := id hτ
  haveI : Nontrivial τ.V := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    exact f0 (LinearMap.ext fun v => by rw [Subsingleton.elim v 0]; simp)
  haveI : Nontrivial π.V := Submodule.nontrivial_iff_ne_bot.2 π.ne_bot
  haveI : Nontrivial (Sm E n) := π.V.injective_subtype.nontrivial
  have hy' : (⟨y, hyπ⟩ : π.V) ∈ fixed (π.locRep w) N :=
    LocEx.mem_fix.2 fun k hk => Subtype.ext (LocEx.mem_fix.1 hy k hk)
  have h1 := iso_abs τ.ρ (π.locRep w) τ.smooth N hNc (iso_top π w τ hτ) p hp _ hy'
  have h2 := lift_inter (π.locRep w) (rw' n w false) π.V.subtype (fun _ _ => rfl) N p ⟨y, hyπ⟩
  rw [h1, map_zero] at h2
  exact h2.symm
