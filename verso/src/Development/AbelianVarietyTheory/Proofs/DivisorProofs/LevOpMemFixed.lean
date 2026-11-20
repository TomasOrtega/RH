import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GaloisRepOfPolarizedCuspidal
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open scoped Classical TensorProduct

noncomputable section

namespace GlobalTheory.TwTrLevel

variable {G : Type} [Group G] {V : Type} [AddCommGroup V] [Module ℂ V]

/- English proof (translation)
Simplify using `[fixed, GlobalTheory.PRep.eig]`.
-/
theorem mem_fixed_iff (ρ : Representation ℂ G V) (H : Subgroup G) (v : V) :
    v ∈ fixed ρ H ↔ ∀ h ∈ H, ρ h v = v := by
  simp [fixed, GlobalTheory.PRep.eig]

/- English proof (translation)
Take `⟨h, hh⟩` from `QuotientGroup.mk_out_eq_mul H g`. Rewrite using `[hh, hF g h h.2]`.
-/
theorem out_eq_of_inv {M : Type} (H : Subgroup G) (F : G → M) (hF : ∀ g, ∀ h ∈ H, F (g * h) = F g) (g : G) :
    F (QuotientGroup.mk g : G ⧸ H).out = F g := by
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul H g
  rw [hh, hF g h h.2]

/- English proof (translation)
Use `haveI := QuotientGroup.discreteTopology hH`. Establish `hc : IsCompact ((QuotientGroup.mk : G → G ⧸ H) '' tsupport f)` using `hf.isCompact.image QuotientGroup.continuous_mk`. Use `hc.finite_of_discrete.subset ?_` and prove the remaining obligations. Introduce `q hq`. Conclude with `⟨q.out, subset_tsupport f hq, QuotientGroup.out_eq' q⟩`.
-/
theorem finite_supp [TopologicalSpace G] [IsTopologicalGroup G] (H : Subgroup G) (hH : IsOpen (H : Set G))
    (f : G → ℂ) (hf : HasCompactSupport f) : {q : G ⧸ H | f q.out ≠ 0}.Finite := by
  haveI := QuotientGroup.discreteTopology hH
  have hc : IsCompact ((QuotientGroup.mk : G → G ⧸ H) '' tsupport f) :=
    hf.isCompact.image QuotientGroup.continuous_mk
  refine hc.finite_of_discrete.subset ?_
  intro q hq
  exact ⟨q.out, subset_tsupport f hq, QuotientGroup.out_eq' q⟩

/- English proof (translation)
Unfold `levOp`. Rewrite using `[LinearMap.smul_apply]`. Use `congr 1`. Use `AddMonoidHom.map_finsum (LinearMap.applyₗ (R := ℂ) (M := V) (M₂ := V) v).toAddMonoidHom (f := fun q : G ⧸ H => f q.out • (ρ q.out ∘ₗ A)) (hs.subset ?_)` as an intermediate fact. Simplify using `using this`.

Introduce `q hq`. Simplify using `only [Function.mem_support, ne_eq, Set.mem_setOf_eq] at hq ⊢`. Introduce `h0`. Conclude with `hq (by rw [h0, zero_smul])`.
-/
theorem levOp_apply (ρ : Representation ℂ G V) (K H : Subgroup G) (f : G → ℂ) (A : V →ₗ[ℂ] V) (v : V)
    (hs : {q : G ⧸ H | f q.out ≠ 0}.Finite) :
    levOp ρ K H f A v = ((H.relIndex K : ℕ) : ℂ)⁻¹ • ∑ᶠ q : G ⧸ H, f q.out • ρ q.out (A v) := by
  unfold levOp
  rw [LinearMap.smul_apply]
  congr 1
  have := AddMonoidHom.map_finsum (LinearMap.applyₗ (R := ℂ) (M := V) (M₂ := V) v).toAddMonoidHom
    (f := fun q : G ⧸ H => f q.out • (ρ q.out ∘ₗ A)) (hs.subset ?_)
  · simpa using this
  · intro q hq
    simp only [Function.mem_support, ne_eq, Set.mem_setOf_eq] at hq ⊢
    intro h0
    exact hq (by rw [h0, zero_smul])

/- English proof (translation)
Rewrite `hw`, the goal using `[mem_fixed_iff]`. Introduce `k hk`. Establish `h1` using `LinearMap.congr_fun (hA (θ k)) w`. Simplify using `only [LinearMap.coe_comp, Function.comp_apply, hθ] at h1`. Rewrite using `[← h1, hw _ (hH k hk)]`.
-/
theorem A_mem_fixed (ρ : Representation ℂ G V) (θ : G →* G) (hθ : ∀ g, θ (θ g) = g) (A : V →ₗ[ℂ] V)
    (hA : ∀ g, A ∘ₗ ρ g = ρ (θ g) ∘ₗ A) (H : Subgroup G) (hH : ∀ k ∈ H, θ k ∈ H) (w : V)
    (hw : w ∈ fixed ρ H) : A w ∈ fixed ρ H := by
  rw [mem_fixed_iff] at hw ⊢
  intro k hk
  have h1 := LinearMap.congr_fun (hA (θ k)) w
  simp only [LinearMap.coe_comp, Function.comp_apply, hθ] at h1
  rw [← h1, hw _ (hH k hk)]

/- English proof (translation)
Establish `hs` using `finite_supp H hHo f hf.1`. Establish `hu` using `A_mem_fixed ρ θ hθ A hA H hH v hv`. Rewrite `hu` using `[mem_fixed_iff]`. Rewrite using `[levOp_apply ρ K H f A v hs, mem_fixed_iff]`. Introduce `k hk`.

Use `set F : G → V := fun g => f g • ρ g (A v) with hFdef`. Establish `hF : ∀ g, ∀ h ∈ H, F (g * h) = F g`. Introduce `g h hh`. Simplify using `only [hFdef, (hf.2 h hh g).2, map_mul, Module.End.mul_apply, hu h hh]`. Establish `hsupp : (Function.support fun q : G ⧸ H => F q.out).Finite`.

Use `hs.subset ?_` and prove the remaining obligations. Introduce `q hq`. Simplify using `only [Function.mem_support, ne_eq, Set.mem_setOf_eq, hFdef] at hq ⊢`. Introduce `h0`. Conclude with `hq (by rw [h0, zero_smul])`.

Rewrite using `[map_smul]`. Use `congr 1`. Express the relevant statement in the definitionally equal form `ρ k (∑ᶠ q : G ⧸ H, F q.out) = ∑ᶠ q : G ⧸ H, F q.out`. Establish `hm` using `AddMonoidHom.map_finsum (ρ k).toAddMonoidHom hsupp`. Simplify using `only [LinearMap.toAddMonoidHom_coe] at hm`.

Rewrite using `[hm]`. Establish `hk' : ∀ q : G ⧸ H, ρ k (F q.out) = F (k • q).out`. Introduce `q`. Establish `e1 : (k • q : G ⧸ H) = QuotientGroup.mk (k * q.out)` using `by conv_lhs => rw [← QuotientGroup.out_eq' q]`. Both sides reduce to the same expression.

Rewrite using `[e1, out_eq_of_inv H F hF]`. Simplify using `only [hFdef, map_smul, map_mul, Module.End.mul_apply, (hf.2 k hk q.out).1]`. Repeatedly rewrite using `[hk']`. Conclude with `finsum_comp_equiv (MulAction.toPerm k : Equiv.Perm (G ⧸ H)) (f := fun q : G ⧸ H => F q.out)`.
-/
theorem levOp_mem_fixed [TopologicalSpace G] [IsTopologicalGroup G] (ρ : Representation ℂ G V) (θ : G →* G)
    (hθ : ∀ g, θ (θ g) = g) (A : V →ₗ[ℂ] V) (hA : ∀ g, A ∘ₗ ρ g = ρ (θ g) ∘ₗ A) (K H : Subgroup G)
    (hHo : IsOpen (H : Set G)) (hH : ∀ k ∈ H, θ k ∈ H) (f : G → ℂ) (hf : IsHecke H f) (v : V)
    (hv : v ∈ fixed ρ H) : levOp ρ K H f A v ∈ fixed ρ H := by
  have hs := finite_supp H hHo f hf.1
  have hu := A_mem_fixed ρ θ hθ A hA H hH v hv
  rw [mem_fixed_iff] at hu
  rw [levOp_apply ρ K H f A v hs, mem_fixed_iff]
  intro k hk
  set F : G → V := fun g => f g • ρ g (A v) with hFdef
  have hF : ∀ g, ∀ h ∈ H, F (g * h) = F g := by
    intro g h hh
    simp only [hFdef, (hf.2 h hh g).2, map_mul, Module.End.mul_apply, hu h hh]
  have hsupp : (Function.support fun q : G ⧸ H => F q.out).Finite := by
    refine hs.subset ?_
    intro q hq
    simp only [Function.mem_support, ne_eq, Set.mem_setOf_eq, hFdef] at hq ⊢
    intro h0
    exact hq (by rw [h0, zero_smul])
  rw [map_smul]
  congr 1
  change ρ k (∑ᶠ q : G ⧸ H, F q.out) = ∑ᶠ q : G ⧸ H, F q.out
  have hm := AddMonoidHom.map_finsum (ρ k).toAddMonoidHom hsupp
  simp only [LinearMap.toAddMonoidHom_coe] at hm
  rw [hm]
  have hk' : ∀ q : G ⧸ H, ρ k (F q.out) = F (k • q).out := by
    intro q
    have e1 : (k • q : G ⧸ H) = QuotientGroup.mk (k * q.out) := by
      conv_lhs => rw [← QuotientGroup.out_eq' q]
      rfl
    rw [e1, out_eq_of_inv H F hF]
    simp only [hFdef, map_smul, map_mul, Module.End.mul_apply, (hf.2 k hk q.out).1]
  simp_rw [hk']
  exact finsum_comp_equiv (MulAction.toPerm k : Equiv.Perm (G ⧸ H)) (f := fun q : G ⧸ H => F q.out)

def avgOp (ρ : Representation ℂ G V) (K' K'' : Subgroup G) : V →ₗ[ℂ] V :=
  ((K''.relIndex K' : ℕ) : ℂ)⁻¹ • ∑ᶠ j : K' ⧸ K''.subgroupOf K', ρ (j.out : G)

/- English proof (translation)
Establish `hc : IsCompact (K' : Set G)` using `hK.of_isClosed_subset (Subgroup.isClosed_of_isOpen K' h') hle`. Use `haveI : CompactSpace K' := isCompact_iff_compactSpace.mp hc`. Establish `ho : IsOpen ((K''.subgroupOf K' : Subgroup K') : Set K')` using `h''.preimage continuous_subtype_val`. Use `haveI := QuotientGroup.discreteTopology ho`. Conclude with `finite_of_compact_of_discrete`.
-/
theorem finite_quot [TopologicalSpace G] [IsTopologicalGroup G] (K K' K'' : Subgroup G)
    (hK : IsCompact (K : Set G)) (h' : IsOpen (K' : Set G)) (h'' : IsOpen (K'' : Set G)) (hle : K' ≤ K) :
    Finite (K' ⧸ K''.subgroupOf K') := by
  have hc : IsCompact (K' : Set G) := hK.of_isClosed_subset (Subgroup.isClosed_of_isOpen K' h') hle
  haveI : CompactSpace K' := isCompact_iff_compactSpace.mp hc
  have ho : IsOpen ((K''.subgroupOf K' : Subgroup K') : Set K') := h''.preimage continuous_subtype_val
  haveI := QuotientGroup.discreteTopology ho
  exact finite_of_compact_of_discrete

/- English proof (translation)
Unfold `avgOp`. Rewrite using `[LinearMap.smul_apply]`. Use `congr 1`. Use `AddMonoidHom.map_finsum (LinearMap.applyₗ (R := ℂ) (M := V) (M₂ := V) u).toAddMonoidHom (f := fun j : K' ⧸ K''.subgroupOf K' => ρ (j.out : G)) (Set.toFinite _)` as an intermediate fact. Simplify using `using this`.
-/
theorem avgOp_apply (ρ : Representation ℂ G V) (K' K'' : Subgroup G) [Finite (K' ⧸ K''.subgroupOf K')] (u : V) :
    avgOp ρ K' K'' u = ((K''.relIndex K' : ℕ) : ℂ)⁻¹ • ∑ᶠ j : K' ⧸ K''.subgroupOf K', ρ (j.out : G) u := by
  unfold avgOp
  rw [LinearMap.smul_apply]
  congr 1
  have := AddMonoidHom.map_finsum (LinearMap.applyₗ (R := ℂ) (M := V) (M₂ := V) u).toAddMonoidHom
    (f := fun j : K' ⧸ K''.subgroupOf K' => ρ (j.out : G)) (Set.toFinite _)
  simpa using this

/- English proof (translation)
Establish `hs'` using `finite_supp K' h'o f hf.1`. Establish `hs''` using `finite_supp K'' h''o f hf.1`. Rewrite `hu` using `[mem_fixed_iff]`. Rewrite using `[levOp_apply ρ K K'' f _ u hs'', levOp_apply ρ K K' f _ _ hs', avgOp_apply]`. Simplify using `only [LinearMap.id_apply]`.

Use `set F : G → V := fun g => f g • ρ g u with hFdef`. Establish `hF : ∀ g, ∀ h ∈ K'', F (g * h) = F g`. Introduce `g h hh`. Simplify using `only [hFdef, (hf.2 h (hle hh) g).2, map_mul, Module.End.mul_apply, hu h hh]`. Use `set e := Subgroup.quotientEquivProdOfLE hle with hedef`.

Establish `he : ∀ (q : G ⧸ K') (j : K' ⧸ K''.subgroupOf K'), F (e.symm (q, j)).out = f q.out • ρ q.out (ρ (j.out : G) u)`. Introduce `q j`. Establish `h1 : e.symm (q, j) = (QuotientGroup.mk (q.out * (j.out : G)) : G ⧸ K'')`. Rewrite using `[hedef, Subgroup.quotientEquivProdOfLE_symm_apply]`. Use `conv_lhs => rw [← QuotientGroup.out_eq' j]`.

Both sides reduce to the same expression. Rewrite using `[h1, out_eq_of_inv K'' F hF]`. Simplify using `only [hFdef, (hf.2 _ (j.out).2 q.out).2, map_mul, Module.End.mul_apply]`. Use `set S : G ⧸ K' → V := fun q => ∑ᶠ j : K' ⧸ K''.subgroupOf K', f q.out • ρ q.out (ρ (j.out : G) u) with hSdef`. Establish `hL : ∑ᶠ r : G ⧸ K'', F r.out = ∑ᶠ q, S q`.

Rewrite using `[← finsum_comp_equiv e.symm]`. Rewrite using `[finsum_curry]`. Simplify using `only [he, hSdef]`. Use `(hs'.prod (Set.finite_univ (α := K' ⧸ K''.subgroupOf K'))).subset ?_` and prove the remaining obligations. Introduce and unpack `⟨q, j⟩ hp`.

Simplify using `only [Function.mem_support, ne_eq, he] at hp`. Simplify using `only [Set.mem_prod, Set.mem_setOf_eq, Set.mem_univ, and_true]`. Introduce `h0`. Conclude with `hp (by rw [h0, zero_smul])`. Establish `hR : ∀ q : G ⧸ K', f q.out • ρ q.out (((K''.relIndex K' : ℕ) : ℂ)⁻¹ • ∑ᶠ j : K' ⧸ K''.subgroupOf K', ρ (j.out : G) u) = ((K''.relIndex K' : ℕ) : ℂ)⁻¹ • S q`.

Introduce `q`. Establish `hm` using `AddMonoidHom.map_finsum (f q.out • ρ q.out).toAddMonoidHom (f := fun j : K' ⧸ K''.subgroupOf K' => ρ (j.out : G) u) (Set.toFinite _)`. Simplify using `only [LinearMap.toAddMonoidHom_coe, LinearMap.smul_apply] at hm`. Rewrite using `[map_smul, smul_comm, hm]`. Simplify using `only [hR]`.

Rewrite using `[hL, ← smul_finsum, smul_smul, ← Subgroup.relIndex_mul_relIndex K'' K' K hle hK'K]`. Use `congr 1`. Use `push_cast`. Rewrite using `[mul_inv, mul_comm]`.
-/
theorem levOp_le [TopologicalSpace G] [IsTopologicalGroup G] (ρ : Representation ℂ G V) (K K' K'' : Subgroup G)
    (hle : K'' ≤ K') (hK'K : K' ≤ K) [Finite (K' ⧸ K''.subgroupOf K')] (h'o : IsOpen (K' : Set G))
    (h''o : IsOpen (K'' : Set G)) (f : G → ℂ) (hf : IsHecke K' f) (u : V) (hu : u ∈ fixed ρ K'') :
    levOp ρ K K'' f LinearMap.id u = levOp ρ K K' f LinearMap.id (avgOp ρ K' K'' u) := by
  have hs' := finite_supp K' h'o f hf.1
  have hs'' := finite_supp K'' h''o f hf.1
  rw [mem_fixed_iff] at hu
  rw [levOp_apply ρ K K'' f _ u hs'', levOp_apply ρ K K' f _ _ hs', avgOp_apply]
  simp only [LinearMap.id_apply]
  set F : G → V := fun g => f g • ρ g u with hFdef
  have hF : ∀ g, ∀ h ∈ K'', F (g * h) = F g := by
    intro g h hh
    simp only [hFdef, (hf.2 h (hle hh) g).2, map_mul, Module.End.mul_apply, hu h hh]
  set e := Subgroup.quotientEquivProdOfLE hle with hedef
  have he : ∀ (q : G ⧸ K') (j : K' ⧸ K''.subgroupOf K'),
      F (e.symm (q, j)).out = f q.out • ρ q.out (ρ (j.out : G) u) := by
    intro q j
    have h1 : e.symm (q, j) = (QuotientGroup.mk (q.out * (j.out : G)) : G ⧸ K'') := by
      rw [hedef, Subgroup.quotientEquivProdOfLE_symm_apply]
      conv_lhs => rw [← QuotientGroup.out_eq' j]
      rfl
    rw [h1, out_eq_of_inv K'' F hF]
    simp only [hFdef, (hf.2 _ (j.out).2 q.out).2, map_mul, Module.End.mul_apply]
  set S : G ⧸ K' → V := fun q => ∑ᶠ j : K' ⧸ K''.subgroupOf K', f q.out • ρ q.out (ρ (j.out : G) u) with hSdef
  have hL : ∑ᶠ r : G ⧸ K'', F r.out = ∑ᶠ q, S q := by
    rw [← finsum_comp_equiv e.symm]
    rw [finsum_curry]
    · simp only [he, hSdef]
    · refine (hs'.prod (Set.finite_univ (α := K' ⧸ K''.subgroupOf K'))).subset ?_
      rintro ⟨q, j⟩ hp
      simp only [Function.mem_support, ne_eq, he] at hp
      simp only [Set.mem_prod, Set.mem_setOf_eq, Set.mem_univ, and_true]
      intro h0
      exact hp (by rw [h0, zero_smul])
  have hR : ∀ q : G ⧸ K', f q.out • ρ q.out (((K''.relIndex K' : ℕ) : ℂ)⁻¹ •
      ∑ᶠ j : K' ⧸ K''.subgroupOf K', ρ (j.out : G) u) = ((K''.relIndex K' : ℕ) : ℂ)⁻¹ • S q := by
    intro q
    have hm := AddMonoidHom.map_finsum (f q.out • ρ q.out).toAddMonoidHom
      (f := fun j : K' ⧸ K''.subgroupOf K' => ρ (j.out : G) u) (Set.toFinite _)
    simp only [LinearMap.toAddMonoidHom_coe, LinearMap.smul_apply] at hm
    rw [map_smul, smul_comm, hm]
  simp only [hR]
  rw [hL, ← smul_finsum, smul_smul, ← Subgroup.relIndex_mul_relIndex K'' K' K hle hK'K]
  congr 1
  push_cast
  rw [mul_inv, mul_comm]

/- English proof (translation)
Rewrite `hu` using `[mem_fixed_iff]`. Rewrite using `[avgOp_apply, mem_fixed_iff]`. Introduce `k hk`. Use `set F : K' → V := fun x => ρ (x : G) u with hFdef`. Establish `hF : ∀ x : K', ∀ h ∈ K''.subgroupOf K', F (x * h) = F x`.

Introduce `x h hh`. Simplify using `only [hFdef, Subgroup.coe_mul, map_mul, Module.End.mul_apply, hu _ (Subgroup.mem_subgroupOf.mp hh)]`. Rewrite using `[map_smul]`. Use `congr 1`. Express the relevant statement in the definitionally equal form `ρ k (∑ᶠ j : K' ⧸ K''.subgroupOf K', F j.out) = ∑ᶠ j : K' ⧸ K''.subgroupOf K', F j.out`.

Establish `hm` using `AddMonoidHom.map_finsum (ρ k).toAddMonoidHom (f := fun j : K' ⧸ K''.subgroupOf K' => F j.out) (Set.toFinite _)`. Simplify using `only [LinearMap.toAddMonoidHom_coe] at hm`. Rewrite using `[hm]`. Establish `hk' : ∀ j : K' ⧸ K''.subgroupOf K', ρ k (F j.out) = F ((⟨k, hk⟩ : K') • j).out`. Introduce `j`.

Establish `e1 : ((⟨k, hk⟩ : K') • j : K' ⧸ K''.subgroupOf K') = QuotientGroup.mk ((⟨k, hk⟩ : K') * j.out)` using `by conv_lhs => rw [← QuotientGroup.out_eq' j]`. Both sides reduce to the same expression. Rewrite using `[e1, out_eq_of_inv _ F hF]`. Simplify using `only [hFdef, Subgroup.coe_mul, map_mul, Module.End.mul_apply]`. Repeatedly rewrite using `[hk']`.

Conclude with `finsum_comp_equiv (MulAction.toPerm (⟨k, hk⟩ : K') : Equiv.Perm (K' ⧸ K''.subgroupOf K')) (f := fun j : K' ⧸ K''.subgroupOf K' => F j.out)`.
-/
theorem avgOp_mem (ρ : Representation ℂ G V) (K' K'' : Subgroup G) [Finite (K' ⧸ K''.subgroupOf K')] (u : V)
    (hu : u ∈ fixed ρ K'') : avgOp ρ K' K'' u ∈ fixed ρ K' := by
  rw [mem_fixed_iff] at hu
  rw [avgOp_apply, mem_fixed_iff]
  intro k hk
  set F : K' → V := fun x => ρ (x : G) u with hFdef
  have hF : ∀ x : K', ∀ h ∈ K''.subgroupOf K', F (x * h) = F x := by
    intro x h hh
    simp only [hFdef, Subgroup.coe_mul, map_mul, Module.End.mul_apply, hu _ (Subgroup.mem_subgroupOf.mp hh)]
  rw [map_smul]
  congr 1
  change ρ k (∑ᶠ j : K' ⧸ K''.subgroupOf K', F j.out) = ∑ᶠ j : K' ⧸ K''.subgroupOf K', F j.out
  have hm := AddMonoidHom.map_finsum (ρ k).toAddMonoidHom (f := fun j : K' ⧸ K''.subgroupOf K' => F j.out)
    (Set.toFinite _)
  simp only [LinearMap.toAddMonoidHom_coe] at hm
  rw [hm]
  have hk' : ∀ j : K' ⧸ K''.subgroupOf K', ρ k (F j.out) = F ((⟨k, hk⟩ : K') • j).out := by
    intro j
    have e1 : ((⟨k, hk⟩ : K') • j : K' ⧸ K''.subgroupOf K') = QuotientGroup.mk ((⟨k, hk⟩ : K') * j.out) := by
      conv_lhs => rw [← QuotientGroup.out_eq' j]
      rfl
    rw [e1, out_eq_of_inv _ F hF]
    simp only [hFdef, Subgroup.coe_mul, map_mul, Module.End.mul_apply]
  simp_rw [hk']
  exact finsum_comp_equiv (MulAction.toPerm (⟨k, hk⟩ : K') : Equiv.Perm (K' ⧸ K''.subgroupOf K'))
    (f := fun j : K' ⧸ K''.subgroupOf K' => F j.out)

/- English proof (translation)
Rewrite `hu` using `[mem_fixed_iff]`. Rewrite using `[avgOp_apply]`. Establish `h1 : ∀ j : K' ⧸ K''.subgroupOf K', ρ (j.out : G) u = u` using `fun j => hu _ (j.out).2`. Simplify using `only [h1]`. Use `haveI := Fintype.ofFinite (K' ⧸ K''.subgroupOf K')`.

Rewrite using `[finsum_eq_sum_of_fintype, Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul]`. Establish `h2 : (K''.relIndex K' : ℕ) = Fintype.card (K' ⧸ K''.subgroupOf K')`. Rewrite using `[Subgroup.relIndex, Subgroup.index, Nat.card_eq_fintype_card]`. Establish `h3 : (Fintype.card (K' ⧸ K''.subgroupOf K') : ℂ) ≠ 0`. Conclude with `(Fintype.card_pos (α := K' ⧸ K''.subgroupOf K')).ne'` after adjusting the coercions.

Rewrite using `[h2, inv_mul_cancel₀ h3, one_smul]`.
-/
theorem avgOp_fix (ρ : Representation ℂ G V) (K' K'' : Subgroup G) [Finite (K' ⧸ K''.subgroupOf K')] (u : V)
    (hu : u ∈ fixed ρ K') : avgOp ρ K' K'' u = u := by
  rw [mem_fixed_iff] at hu
  rw [avgOp_apply]
  have h1 : ∀ j : K' ⧸ K''.subgroupOf K', ρ (j.out : G) u = u := fun j => hu _ (j.out).2
  simp only [h1]
  haveI := Fintype.ofFinite (K' ⧸ K''.subgroupOf K')
  rw [finsum_eq_sum_of_fintype, Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
  have h2 : (K''.relIndex K' : ℕ) = Fintype.card (K' ⧸ K''.subgroupOf K') := by
    rw [Subgroup.relIndex, Subgroup.index, Nat.card_eq_fintype_card]
  have h3 : (Fintype.card (K' ⧸ K''.subgroupOf K') : ℂ) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos (α := K' ⧸ K''.subgroupOf K')).ne'
  rw [h2, inv_mul_cancel₀ h3, one_smul]

end GlobalTheory.TwTrLevel
