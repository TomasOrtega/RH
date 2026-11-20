import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.Distinct
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Brauer
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.DcGelfand
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.SelmerDuality.HasSmithOfOne
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

/- English proof (translation)
Use `haveI : DiscreteTopology (G ⧸ K) := QuotientGroup.discreteTopology hK'`. Establish `hc : Continuous fun g : G => ((g * x : G) : G ⧸ K)` using `QuotientGroup.continuous_mk.comp (continuous_id.mul continuous_const)`. Use `((hL.image hc).finite_of_discrete).subset ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨g, rfl⟩`. Conclude with `⟨g, g.2, rfl⟩`.
-/
private theorem sphC_fin {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {K : Subgroup G} (hL : IsCompact (K : Set G)) (hK' : IsOpen (K : Set G)) (x : G) :
    (MulAction.orbit K (x : G ⧸ K)).Finite := by
  haveI : DiscreteTopology (G ⧸ K) := QuotientGroup.discreteTopology hK'
  have hc : Continuous fun g : G => ((g * x : G) : G ⧸ K) :=
    QuotientGroup.continuous_mk.comp (continuous_id.mul continuous_const)
  refine ((hL.image hc).finite_of_discrete).subset ?_
  rintro _ ⟨g, rfl⟩
  exact ⟨g, g.2, rfl⟩

/- English proof (translation)
Use `Set.ncard_le_ncard_of_injOn (fun q => ((θ q.out : H) : H ⧸ K)) ?_ ?_ (hfin _)` and prove the remaining obligations. Introduce and unpack `q ⟨a, ha⟩`. Establish `h : (((a : H) * x : H) : H ⧸ K) = (q.out : H ⧸ K)`. Rewrite using `[QuotientGroup.out_eq']`. Conclude with `ha`.

Establish `h1` using `hK _ (QuotientGroup.eq.mp h)`. Take `⟨l, hl, l', hl', h2⟩` from `hd x⁻¹`. Rewrite `h2` using `[inv_inv]`. Use `⟨⟨θ a * l, mul_mem (hK _ a.2) hl⟩, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `((θ a * l * x⁻¹ : H) : H ⧸ K) = _`.

Use `QuotientGroup.eq.mpr ?_` and prove the remaining obligations. Establish `h3 : (θ a * l * x⁻¹)⁻¹ * θ q.out = l' * θ (((a : H) * x)⁻¹ * q.out)`. Rewrite using `[map_mul, map_inv, map_mul, h2]`. Use `group`. Rewrite using `[h3]`.

Conclude with `mul_mem hl' h1`. Introduce `p _ q _ h`. Establish `h1` using `hK _ (QuotientGroup.eq.mp h)`. Rewrite `h1` using `[← map_inv, ← map_mul, hθ]`. Rewrite using `[← QuotientGroup.out_eq' p, ← QuotientGroup.out_eq' q]`.

Conclude with `QuotientGroup.eq.mpr h1`.
-/
private theorem sphC_le {H : Type} [Group H] (K : Subgroup H) (θ : H →* H) (hθ : ∀ x, θ (θ x) = x)
    (hK : ∀ k ∈ K, θ k ∈ K) (hd : ∀ x, ∃ k ∈ K, ∃ k' ∈ K, θ x⁻¹ = k * x * k')
    (hfin : ∀ x : H, (MulAction.orbit K (x : H ⧸ K)).Finite) (x : H) :
    (MulAction.orbit K (x : H ⧸ K)).ncard ≤ (MulAction.orbit K ((x⁻¹ : H) : H ⧸ K)).ncard := by
  refine Set.ncard_le_ncard_of_injOn (fun q => ((θ q.out : H) : H ⧸ K)) ?_ ?_ (hfin _)
  · rintro q ⟨a, ha⟩
    have h : (((a : H) * x : H) : H ⧸ K) = (q.out : H ⧸ K) := by
      rw [QuotientGroup.out_eq']; exact ha
    have h1 := hK _ (QuotientGroup.eq.mp h)
    obtain ⟨l, hl, l', hl', h2⟩ := hd x⁻¹
    rw [inv_inv] at h2
    refine ⟨⟨θ a * l, mul_mem (hK _ a.2) hl⟩, ?_⟩
    change ((θ a * l * x⁻¹ : H) : H ⧸ K) = _
    refine QuotientGroup.eq.mpr ?_
    have h3 : (θ a * l * x⁻¹)⁻¹ * θ q.out = l' * θ (((a : H) * x)⁻¹ * q.out) := by
      rw [map_mul, map_inv, map_mul, h2]; group
    rw [h3]
    exact mul_mem hl' h1
  · intro p _ q _ h
    have h1 := hK _ (QuotientGroup.eq.mp h)
    rw [← map_inv, ← map_mul, hθ] at h1
    rw [← QuotientGroup.out_eq' p, ← QuotientGroup.out_eq' q]
    exact QuotientGroup.eq.mpr h1

/- English proof (translation)
Establish `ho : MulAction.orbit K (z : H ⧸ K) = {(z : H ⧸ K)}`. Use extensionality with `q`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨a, rfl⟩`. Express the relevant statement in the definitionally equal form `(((a : H) * z : H) : H ⧸ K) = _`.

Rewrite using `[hz]`. Conclude with `QuotientGroup.eq.mpr (by simp)`. Introduce and unpack `rfl`. Conclude with `MulAction.mem_orbit_self _`. Rewrite using `[dc, finsum_set_coe_eq_finsum_mem (f := fun q : H ⧸ K => ρ q.out), ho, finsum_mem_singleton]`.

Take `⟨m, hm⟩` from `QuotientGroup.mk_out_eq_mul K z`. Rewrite using `[hm, map_mul, Module.End.mul_apply, hv m m.2]`.
-/
private theorem sphC_central {A H M : Type} [CommRing A] [Group H] [AddCommGroup M] [Module A M]
    (ρ : Representation A H M) (K : Subgroup H) (z : H) (hz : ∀ g, g * z = z * g) (v : M) (hv : v ∈ fixd ρ K) :
    dc ρ K K z v = ρ z v := by
  have ho : MulAction.orbit K (z : H ⧸ K) = {(z : H ⧸ K)} := by
    ext q
    constructor
    · rintro ⟨a, rfl⟩
      change (((a : H) * z : H) : H ⧸ K) = _
      rw [hz]
      exact QuotientGroup.eq.mpr (by simp)
    · rintro rfl
      exact MulAction.mem_orbit_self _
  rw [dc, finsum_set_coe_eq_finsum_mem (f := fun q : H ⧸ K => ρ q.out), ho, finsum_mem_singleton]
  obtain ⟨m, hm⟩ := QuotientGroup.mk_out_eq_mul K z
  rw [hm, map_mul, Module.End.mul_apply, hv m m.2]

/- English proof (translation)
Rewrite `hg`, the goal using `[GlobalTheory.SplitFlip.mem_KO_iff]`. Conclude with `⟨fun i j => hg.2 j i, fun i j => hg.1 j i⟩`.
-/
private theorem sphC_invT {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {n : ℕ} (g : GL (Fin n) k) (hg : g ∈ KO k (Fin n)) : GlobalTheory.CuspRep.invT n k g ∈ KO k (Fin n) := by
  rw [GlobalTheory.SplitFlip.mem_KO_iff] at hg ⊢
  exact ⟨fun i j => hg.2 j i, fun i j => hg.1 j i⟩

/- English proof (translation)
Take `⟨c, hc⟩` from `IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors 𝒪[k]) (fun p : Fin n × Fin n => g.val p.1 p.2)`. Use `choose f hf using hc`. Take `⟨U, V, d, hU, hV, hΦ, -⟩` from `KStar.Selmer.exists_smith n (Matrix.of fun i j => f (i, j))`. Take `⟨u, rfl⟩` from `(Matrix.isUnit_iff_isUnit_det U).2 hU`. Take `⟨w, rfl⟩` from `(Matrix.isUnit_iff_isUnit_det V).2 hV`.

Use `set u' : GL (Fin n) k := Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) u with hu'`. Use `set w' : GL (Fin n) k := Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) w with hw'`. Establish `hu : u' ∈ KO k (Fin n)` using `⟨u, rfl⟩`. Establish `hw : w' ∈ KO k (Fin n)` using `⟨w, rfl⟩`. Establish `hc0 : algebraMap 𝒪[k] k c ≠ 0` using `fun h => nonZeroDivisors.ne_zero c.2 (Subtype.ext h)`.

Establish `h1 : algebraMap 𝒪[k] k c • g.val = u'.val * Matrix.diagonal (fun i => algebraMap 𝒪[k] k (d i)) * w'.val`. Establish `h2` using `congrArg (algebraMap 𝒪[k] k).mapMatrix hΦ`. Rewrite `h2` using `[map_mul, map_mul, RingHom.mapMatrix_apply (M := Matrix.diagonal d), Matrix.diagonal_map (map_zero _)]`. Use `Eq.trans ?_ h2` and prove the remaining obligations. Use extensionality with `i j`.

Conclude with `(hf (i, j)).symm`. Establish `h3 : algebraMap 𝒪[k] k c • (u'⁻¹ * g * w'⁻¹).val = Matrix.diagonal (fun i => algebraMap 𝒪[k] k (d i))`. Rewrite using `[Units.val_mul, Units.val_mul, ← smul_mul_assoc, ← mul_smul_comm, h1]`. Simplify using `only [← mul_assoc, Units.inv_mul, one_mul]`. Rewrite using `[mul_assoc, Units.mul_inv, mul_one]`.

Establish `h4 : GlobalTheory.CuspRep.invT n k (u'⁻¹ * g * w'⁻¹)⁻¹ = u'⁻¹ * g * w'⁻¹`. Apply `Units.ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `(u'⁻¹ * g * w'⁻¹).val.transpose = _`. Apply `smul_right_injective _ hc0` to reduce the goal to its premises. Simplify using `only`.

Rewrite using `[← Matrix.transpose_smul, h3, Matrix.diagonal_transpose]`. Use `⟨GlobalTheory.CuspRep.invT n k w'⁻¹ * u'⁻¹, mul_mem (sphC_invT _ (inv_mem hw)) (inv_mem hu), w'⁻¹ * GlobalTheory.CuspRep.invT n k u'⁻¹, mul_mem (inv_mem hw) (sphC_invT _ (inv_mem hu)), ?_⟩` and prove the remaining obligations. Establish `h5 : g⁻¹ = w'⁻¹ * (u'⁻¹ * g * w'⁻¹)⁻¹ * u'⁻¹` using `by group`. Rewrite using `[h5, map_mul, map_mul, h4]`. Simplify using `only [mul_assoc]`.
-/
private theorem sphC_cartan {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {n : ℕ} (g : GL (Fin n) k) :
    ∃ a ∈ KO k (Fin n), ∃ b ∈ KO k (Fin n), GlobalTheory.CuspRep.invT n k g⁻¹ = a * g * b := by
  obtain ⟨c, hc⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors 𝒪[k])
    (fun p : Fin n × Fin n => g.val p.1 p.2)
  choose f hf using hc
  obtain ⟨U, V, d, hU, hV, hΦ, -⟩ := KStar.Selmer.exists_smith n (Matrix.of fun i j => f (i, j))
  obtain ⟨u, rfl⟩ := (Matrix.isUnit_iff_isUnit_det U).2 hU
  obtain ⟨w, rfl⟩ := (Matrix.isUnit_iff_isUnit_det V).2 hV
  set u' : GL (Fin n) k := Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) u with hu'
  set w' : GL (Fin n) k := Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) w with hw'
  have hu : u' ∈ KO k (Fin n) := ⟨u, rfl⟩
  have hw : w' ∈ KO k (Fin n) := ⟨w, rfl⟩
  have hc0 : algebraMap 𝒪[k] k c ≠ 0 := fun h =>
    nonZeroDivisors.ne_zero c.2 (Subtype.ext h)
  have h1 : algebraMap 𝒪[k] k c • g.val =
      u'.val * Matrix.diagonal (fun i => algebraMap 𝒪[k] k (d i)) * w'.val := by
    have h2 := congrArg (algebraMap 𝒪[k] k).mapMatrix hΦ
    rw [map_mul, map_mul, RingHom.mapMatrix_apply (M := Matrix.diagonal d), Matrix.diagonal_map (map_zero _)] at h2
    refine Eq.trans ?_ h2
    ext i j
    exact (hf (i, j)).symm
  have h3 : algebraMap 𝒪[k] k c • (u'⁻¹ * g * w'⁻¹).val = Matrix.diagonal (fun i => algebraMap 𝒪[k] k (d i)) := by
    rw [Units.val_mul, Units.val_mul, ← smul_mul_assoc, ← mul_smul_comm, h1]
    simp only [← mul_assoc, Units.inv_mul, one_mul]
    rw [mul_assoc, Units.mul_inv, mul_one]
  have h4 : GlobalTheory.CuspRep.invT n k (u'⁻¹ * g * w'⁻¹)⁻¹ = u'⁻¹ * g * w'⁻¹ := by
    apply Units.ext
    change (u'⁻¹ * g * w'⁻¹).val.transpose = _
    apply smul_right_injective _ hc0
    simp only
    rw [← Matrix.transpose_smul, h3, Matrix.diagonal_transpose]
  refine ⟨GlobalTheory.CuspRep.invT n k w'⁻¹ * u'⁻¹, mul_mem (sphC_invT _ (inv_mem hw)) (inv_mem hu),
    w'⁻¹ * GlobalTheory.CuspRep.invT n k u'⁻¹, mul_mem (inv_mem hw) (sphC_invT _ (inv_mem hu)), ?_⟩
  have h5 : g⁻¹ = w'⁻¹ * (u'⁻¹ * g * w'⁻¹)⁻¹ * u'⁻¹ := by group
  rw [h5, map_mul, map_mul, h4]
  simp only [mul_assoc]

/- English proof (translation)
Introduce `k _ _ _ _ n A M _ _ _ ρ`. Establish `hfin : ∀ x : GL (Fin n) k, (MulAction.orbit (KO k (Fin n)) (x : GL (Fin n) k ⧸ KO k (Fin n))).Finite` using `sphC_fin GlobalTheory.SplitFlip.isCompact_KO GlobalTheory.SplitFlip.isOpen_KO`. Establish `hθ : ∀ x, GlobalTheory.CuspRep.invT n k (GlobalTheory.CuspRep.invT n k x) = x` using `fun x => Units.ext rfl`. Establish `hle` using `sphC_le (KO k (Fin n)) (GlobalTheory.CuspRep.invT n k) hθ sphC_invT sphC_cartan hfin`. Use `⟨hfin, ?_, fun v hv => ⟨?_, ?_⟩⟩` and prove the remaining obligations.

Use `dcGelfand A _ M ρ _ (fun x => GlobalTheory.CuspRep.invT n k x⁻¹) ?_ ?_ ?_ sphC_cartan hfin ?_` and prove the remaining obligations. Introduce `x y`. Rewrite using `[mul_inv_rev, map_mul]`. Introduce `x`. Rewrite using `[← map_inv, inv_inv, hθ]`.

Introduce `a ha`. Conclude with `sphC_invT _ (inv_mem ha)`. Introduce `x`. Use `le_antisymm (hle x) ?_` and prove the remaining obligations. Simplify using `using hle x⁻¹`.

Establish `h1 : al k n 0 = 1`. Rewrite using `[al, upow, ← (diagT k (Fin n)).map_one]`. Use `congr 1`. Use function extensionality and compare the values at `i`. Simplify using the standard rewrite rules.

Rewrite using `[sphOp, h1, sphC_central ρ _ 1 (by simp) v hv, map_one, Module.End.one_apply]`. Use `sphC_central ρ _ _ (fun g => Units.ext ?_) v hv` and prove the remaining obligations. Establish `h1 : (al k n n).val = Matrix.scalar (Fin n) (unif k : k)`. Rewrite using `[al, upow, val_diagT, Matrix.scalar_apply]`. Use `congr 1`.

Use function extensionality and compare the values at `i`. Simplify using the standard rewrite rules. Rewrite using `[Units.val_mul, Units.val_mul, h1]`. Conclude with `(Matrix.scalar_commute _ (fun _ => Commute.all _ _) _).eq.symm`.
-/
theorem UpperTheory.V.Hi.sphComm :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (A M : Type) [CommRing A] [AddCommGroup M] [Module A M] (ρ : Representation A (GL (Fin n) k) M), (∀ x : GL (Fin n) k, (MulAction.orbit (KO k (Fin n)) (x : GL (Fin n) k ⧸ KO k (Fin n))).Finite) ∧ (∀ x y, ∀ v ∈ fixd ρ (KO k (Fin n)), dc ρ (KO k (Fin n)) (KO k (Fin n)) x (dc ρ (KO k (Fin n)) (KO k (Fin n)) y v) = dc ρ (KO k (Fin n)) (KO k (Fin n)) y (dc ρ (KO k (Fin n)) (KO k (Fin n)) x v)) ∧ ∀ v ∈ fixd ρ (KO k (Fin n)), sphOp ρ 0 v = v ∧ sphOp ρ n v = ρ (al k n n) v := by
  intro k _ _ _ _ n A M _ _ _ ρ
  have hfin : ∀ x : GL (Fin n) k, (MulAction.orbit (KO k (Fin n)) (x : GL (Fin n) k ⧸ KO k (Fin n))).Finite :=
    sphC_fin GlobalTheory.SplitFlip.isCompact_KO GlobalTheory.SplitFlip.isOpen_KO
  have hθ : ∀ x, GlobalTheory.CuspRep.invT n k (GlobalTheory.CuspRep.invT n k x) = x := fun x => Units.ext rfl
  have hle := sphC_le (KO k (Fin n)) (GlobalTheory.CuspRep.invT n k) hθ sphC_invT sphC_cartan hfin
  refine ⟨hfin, ?_, fun v hv => ⟨?_, ?_⟩⟩
  · refine dcGelfand A _ M ρ _ (fun x => GlobalTheory.CuspRep.invT n k x⁻¹) ?_ ?_ ?_ sphC_cartan hfin ?_
    · intro x y
      rw [mul_inv_rev, map_mul]
    · intro x
      rw [← map_inv, inv_inv, hθ]
    · intro a ha
      exact sphC_invT _ (inv_mem ha)
    · intro x
      refine le_antisymm (hle x) ?_
      simpa using hle x⁻¹
  · have h1 : al k n 0 = 1 := by
      rw [al, upow, ← (diagT k (Fin n)).map_one]
      congr 1
      funext i
      simp
    rw [sphOp, h1, sphC_central ρ _ 1 (by simp) v hv, map_one, Module.End.one_apply]
  · refine sphC_central ρ _ _ (fun g => Units.ext ?_) v hv
    have h1 : (al k n n).val = Matrix.scalar (Fin n) (unif k : k) := by
      rw [al, upow, val_diagT, Matrix.scalar_apply]
      congr 1
      funext i
      simp
    rw [Units.val_mul, Units.val_mul, h1]
    exact (Matrix.scalar_commute _ (fun _ => Commute.all _ _) _).eq.symm
