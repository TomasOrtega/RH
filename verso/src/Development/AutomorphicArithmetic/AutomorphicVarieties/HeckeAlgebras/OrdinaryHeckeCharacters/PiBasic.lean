import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.CoefficientRepTrivialOnUnramified
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.GalUnitary
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.OrdProj
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.SpStab
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.HiComm
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.SphComm
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HidaCompleteRings.LocIdem
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.PbMem

section Helpers
open IsLocalRing Matrix UpperTheory.V.Hi

section Gen

variable {A M ι : Type} [CommRing A] [AddCommGroup M] [Module A M]

/- English proof (translation)
Proceed by induction on `r using MonoidAlgebra.induction_linear with`. Consider the case `zero => simp`. Consider the case `add a b ha hb => simp only [map_add, LinearMap.add_apply, ha, hb]`. Consider the case `single g a => simp [h]`.
-/
private theorem pb_mono {N : Type} [AddCommGroup N] [Module A N] {G G' : Type} [Group G] [Group G'] (e : G →* G')
    (ρ : Representation A G M) (ρ' : Representation A G' N) (i : M →ₗ[A] N) (h : ∀ g x, i (ρ g x) = ρ' (e g) (i x))
    (r : MonoidAlgebra A G) (x : M) :
    i (ρ.asAlgebraHom r x) = ρ'.asAlgebraHom (MonoidAlgebra.mapDomainRingHom A e r) (i x) := by
  induction r using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => simp only [map_add, LinearMap.add_apply, ha, hb]
  | single g a => simp [h]

/- English proof (translation)
Set `ρ1 : Representation A G N` to `ρ'.comp e.toMonoidHom`. Establish `h1 : Module.Projective (MonoidAlgebra A G) ρ1.asModule`. Set `σ : MonoidAlgebra A G' ≃+* MonoidAlgebra A G` to `(MonoidAlgebra.domCongr A A e.symm).toRingEquiv`. Use `letI := RingHomInvPair.of_ringEquiv σ`. Use `letI := RingHomInvPair.of_ringEquiv_symm σ`.

Set `E : ρ'.asModule ≃ₛₗ[(σ : MonoidAlgebra A G' →+* MonoidAlgebra A G)] ρ1.asModule` to `{ toFun := fun x => x invFun := fun x => x map_add' := fun _ _ => rfl left_inv := fun _ => rfl right_inv := fun _ => rfl map_smul' := fun r x => pb_mono e.symm.toMonoidHom ρ' ρ1 LinearMap.id (fun g x => by simp [ρ1]) r x }`. Conclude with `Module.Projective.of_equiv E`. Set `I : ρ.asModule →ₗ[MonoidAlgebra A G] ρ1.asModule` to `{ toFun := fun x => i x map_add' := fun x y => i.map_add x y map_smul' := fun r x => by`. Use `pb_mono (MonoidHom.id G) ρ ρ1 i h r x` as an intermediate fact. Simplify using `at this`.

Conclude with `this }`. Set `P : ρ1.asModule →ₗ[MonoidAlgebra A G] ρ.asModule` to `{ toFun := fun x => p x map_add' := fun x y => p.map_add x y map_smul' := fun r x => by`. Use `pb_mono (MonoidHom.id G) ρ1 ρ p h' r x` as an intermediate fact. Simplify using `at this`. Conclude with `this }`.

Conclude with `Module.Projective.of_split I P (LinearMap.ext hp)`.
-/
private theorem pb_proj {N : Type} [AddCommGroup N] [Module A N] {G G' : Type} [Group G] [Group G'] (e : G ≃* G')
    (ρ : Representation A G M) (ρ' : Representation A G' N) (i : M →ₗ[A] N) (p : N →ₗ[A] M) (hp : ∀ x, p (i x) = x)
    (h : ∀ g x, i (ρ g x) = ρ' (e g) (i x)) (h' : ∀ g x, p (ρ' (e g) x) = ρ g (p x))
    (hP : Module.Projective (MonoidAlgebra A G') ρ'.asModule) : Module.Projective (MonoidAlgebra A G) ρ.asModule := by
  let ρ1 : Representation A G N := ρ'.comp e.toMonoidHom
  have h1 : Module.Projective (MonoidAlgebra A G) ρ1.asModule := by
    let σ : MonoidAlgebra A G' ≃+* MonoidAlgebra A G := (MonoidAlgebra.domCongr A A e.symm).toRingEquiv
    letI := RingHomInvPair.of_ringEquiv σ
    letI := RingHomInvPair.of_ringEquiv_symm σ
    let E : ρ'.asModule ≃ₛₗ[(σ : MonoidAlgebra A G' →+* MonoidAlgebra A G)] ρ1.asModule :=
      { toFun := fun x => x
        invFun := fun x => x
        map_add' := fun _ _ => rfl
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl
        map_smul' := fun r x => pb_mono e.symm.toMonoidHom ρ' ρ1 LinearMap.id (fun g x => by simp [ρ1]) r x }
    exact Module.Projective.of_equiv E
  let I : ρ.asModule →ₗ[MonoidAlgebra A G] ρ1.asModule :=
    { toFun := fun x => i x
      map_add' := fun x y => i.map_add x y
      map_smul' := fun r x => by
        have := pb_mono (MonoidHom.id G) ρ ρ1 i h r x
        simp at this
        exact this }
  let P : ρ1.asModule →ₗ[MonoidAlgebra A G] ρ.asModule :=
    { toFun := fun x => p x
      map_add' := fun x y => p.map_add x y
      map_smul' := fun r x => by
        have := pb_mono (MonoidHom.id G) ρ1 ρ p h' r x
        simp at this
        exact this }
  exact Module.Projective.of_split I P (LinearMap.ext hp)

/- English proof (translation)
The claim follows from `(iSup_le fun n x hx => Submodule.mem_iSup_of_mem n (h n x hx) : (⨆ n, S n) ≤ (⨆ n, S' n).comap φ)`.
-/
private theorem pb_iSup {S S' : ℕ → Submodule A M} (φ : Module.End A M) (h : ∀ n, ∀ x ∈ S n, φ x ∈ S' n) :
    ∀ x ∈ ⨆ n, S n, φ x ∈ ⨆ n, S' n :=
  (iSup_le fun n x hx => Submodule.mem_iSup_of_mem n (h n x hx) : (⨆ n, S n) ≤ (⨆ n, S' n).comap φ)

/- English proof (translation)
Introduce `x hx` and use `Submodule.smul_induction_on hx (fun r hr z hz => by rw [map_smul]; exact Submodule.smul_mem_smul hr (h z hz)) fun a b ha hb => by rw [map_add]; exact add_mem ha hb`.
-/
private theorem pb_smul {Y Y' : Submodule A M} (φ : Module.End A M) (h : ∀ x ∈ Y, φ x ∈ Y') (J : Ideal A) :
    ∀ x ∈ J • Y, φ x ∈ J • Y' := fun x hx =>
  Submodule.smul_induction_on hx (fun r hr z hz => by rw [map_smul]; exact Submodule.smul_mem_smul hr (h z hz))
    fun a b ha hb => by rw [map_add]; exact add_mem ha hb

variable [IsLocalRing A]

/- English proof (translation)
Introduce `x hx`. Use `⟨h x hx.1, ?_⟩` and prove the remaining obligations. Establish `h2` using `hx.2`. Simplify using `only [SetLike.mem_coe, Submodule.mem_iInf] at h2 ⊢`. Introduce `i k`.

Use `pb_iSup φ (fun n y hy => ?_) x (h2 i k)` and prove the remaining obligations. Establish `hc' : Commute φ ((op i - algebraMap A _ (a i)) ^ n)` using `((hc i).sub_right (Algebra.commutes (a i) φ).symm).pow_right n`. Rewrite using `[Submodule.mem_comap, ← Module.End.mul_apply, ← hc'.eq, Module.End.mul_apply]`. Conclude with `pb_smul φ h _ _ hy`.
-/
private theorem pb_locMap {Y Y' : Submodule A M} (op : ι → Module.End A M) (a : ι → A) (φ : Module.End A M)
    (h : ∀ x ∈ Y, φ x ∈ Y') (hc : ∀ i, Commute φ (op i)) : ∀ x ∈ locPart Y op a, φ x ∈ locPart Y' op a := by
  intro x hx
  refine ⟨h x hx.1, ?_⟩
  have h2 := hx.2
  simp only [SetLike.mem_coe, Submodule.mem_iInf] at h2 ⊢
  intro i k
  refine pb_iSup φ (fun n y hy => ?_) x (h2 i k)
  have hc' : Commute φ ((op i - algebraMap A _ (a i)) ^ n) :=
    ((hc i).sub_right (Algebra.commutes (a i) φ).symm).pow_right n
  rw [Submodule.mem_comap, ← Module.End.mul_apply, ← hc'.eq, Module.End.mul_apply]
  exact pb_smul φ h _ _ hy

/- English proof (translation)
Introduce `x hx hY`. Use `⟨hY, ?_⟩` and prove the remaining obligations. Establish `h2` using `hx.2`. Simplify using `only [SetLike.mem_coe, Submodule.mem_iInf] at h2 ⊢`. Introduce `i k`.

Take `⟨c, hc⟩` from `Ideal.exists_pow_inf_eq_pow_smul (maximalIdeal A) (Y.comap Y'.subtype)`. Use `set T := op i - algebraMap A _ (a i)`. Establish `hT : ∀ n : ℕ, ∀ x ∈ Y, (T ^ n) x ∈ Y`. Introduce `n x hx`. Proceed by induction on `n with`.

Consider the case `zero => simpa using hx`. Consider the case `succ n ih`. Rewrite using `[pow_succ', Module.End.mul_apply]`. Conclude with `sub_mem (h i _ ih) (Y.smul_mem _ ih)`. Establish `hmono : Monotone fun n : ℕ => (maximalIdeal A ^ (k + c) • Y').comap (T ^ n)`.

Use `monotone_nat_of_le_succ fun n x hx => ?_` and prove the remaining obligations. Rewrite `hx`, the goal using `[Submodule.mem_comap]`. Rewrite using `[pow_succ', Module.End.mul_apply]`. Conclude with `pb_smul T (fun y hy => sub_mem (h' i _ hy) (Y'.smul_mem _ hy)) _ _ hx`. Take `⟨n, hn⟩` from `(Submodule.mem_iSup_of_directed _ hmono.directed_le).1 (h2 i (k + c))`.

Use `Submodule.mem_iSup_of_mem n ?_` and prove the remaining obligations. Rewrite `hn`, the goal using `[Submodule.mem_comap]`. Establish `h3 : (⟨(T ^ n) x, hle (hT n x hY)⟩ : Y') ∈ maximalIdeal A ^ (k + c) • ⊤ ⊓ Y.comap Y'.subtype` using `⟨(Submodule.mem_smul_top_iff _ _ _).2 hn, hT n x hY⟩`. Rewrite `h3` using `[hc (k + c) (Nat.le_add_left _ _), Nat.add_sub_cancel]`. Establish `h4` using `Submodule.mem_map_of_mem (f := Y'.subtype) h3`.

Rewrite `h4` using `[Submodule.map_smul'']`. Use `Submodule.smul_mono le_rfl ?_ h4` and prove the remaining obligations. Introduce and unpack `_ ⟨y, hy, rfl⟩`. Conclude with `hy.2`.
-/
private theorem pb_locInf [IsNoetherianRing A] {Y Y' : Submodule A M} [Module.Finite A Y'] (op : ι → Module.End A M) (a : ι → A)
    (hle : Y ≤ Y') (h : ∀ i, ∀ x ∈ Y, op i x ∈ Y) (h' : ∀ i, ∀ x ∈ Y', op i x ∈ Y') : ∀ x ∈ locPart Y' op a, x ∈ Y → x ∈ locPart Y op a := by
  intro x hx hY
  refine ⟨hY, ?_⟩
  have h2 := hx.2
  simp only [SetLike.mem_coe, Submodule.mem_iInf] at h2 ⊢
  intro i k
  obtain ⟨c, hc⟩ := Ideal.exists_pow_inf_eq_pow_smul (maximalIdeal A) (Y.comap Y'.subtype)
  set T := op i - algebraMap A _ (a i)
  have hT : ∀ n : ℕ, ∀ x ∈ Y, (T ^ n) x ∈ Y := by
    intro n x hx
    induction n with
    | zero => simpa using hx
    | succ n ih =>
      rw [pow_succ', Module.End.mul_apply]
      exact sub_mem (h i _ ih) (Y.smul_mem _ ih)
  have hmono : Monotone fun n : ℕ => (maximalIdeal A ^ (k + c) • Y').comap (T ^ n) := by
    refine monotone_nat_of_le_succ fun n x hx => ?_
    rw [Submodule.mem_comap] at hx ⊢
    rw [pow_succ', Module.End.mul_apply]
    exact pb_smul T (fun y hy => sub_mem (h' i _ hy) (Y'.smul_mem _ hy)) _ _ hx
  obtain ⟨n, hn⟩ := (Submodule.mem_iSup_of_directed _ hmono.directed_le).1 (h2 i (k + c))
  refine Submodule.mem_iSup_of_mem n ?_
  rw [Submodule.mem_comap] at hn ⊢
  have h3 : (⟨(T ^ n) x, hle (hT n x hY)⟩ : Y') ∈ maximalIdeal A ^ (k + c) • ⊤ ⊓ Y.comap Y'.subtype :=
    ⟨(Submodule.mem_smul_top_iff _ _ _).2 hn, hT n x hY⟩
  rw [hc (k + c) (Nat.le_add_left _ _), Nat.add_sub_cancel] at h3
  have h4 := Submodule.mem_map_of_mem (f := Y'.subtype) h3
  rw [Submodule.map_smul''] at h4
  refine Submodule.smul_mono le_rfl ?_ h4
  rintro _ ⟨y, hy, rfl⟩
  exact hy.2

end Gen

section Fr

variable {Γ Ga Gp : Type} [Group Γ] [Group Ga] [Group Gp] (X : Frame Γ Ga Gp) {A : Type} [CommRing A] {m : ℕ}
  (τ : X.Ub →* GL (Fin m) A) (θ : X.I.T →* Aˣ)

/- English proof (translation)
Unfold `Frame.U Iwa.uOp`. Use `finsum_induction (fun t => Commute (X.ra τ u) t) (Commute.zero_right _) (fun _ _ => Commute.add_right) fun q => ?_` and prove the remaining obligations. Use `LinearMap.ext fun f => funext fun g => ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(τ u : Matrix (Fin m) (Fin m) A) *ᵥ f (g * ((u : Ga), 1) * (1, _)) = (τ u : Matrix (Fin m) (Fin m) A) *ᵥ f (g * (1, _) * ((u : Ga), 1))`. Simplify using `[mul_assoc]`.
-/
private theorem pb_commU (u : X.Ub) (b : Gp) : Commute (X.ra τ u) (X.U A m b) := by
  unfold Frame.U Iwa.uOp
  refine finsum_induction (fun t => Commute (X.ra τ u) t) (Commute.zero_right _) (fun _ _ => Commute.add_right) fun q => ?_
  refine LinearMap.ext fun f => funext fun g => ?_
  change (τ u : Matrix (Fin m) (Fin m) A) *ᵥ f (g * ((u : Ga), 1) * (1, _)) =
    (τ u : Matrix (Fin m) (Fin m) A) *ᵥ f (g * (1, _) * ((u : Ga), 1))
  simp [mul_assoc]

/- English proof (translation)
Use `⟨⟨(spStab _ _ _ X A m τ θ hθ).2.1 u f hf.1.1, h⟩, ?_⟩` and prove the remaining obligations. Establish `h2` using `hf.2`. Simplify using `only [SetLike.mem_coe, Submodule.mem_iInf] at h2 ⊢`. Introduce `k`. Use `pb_iSup _ (fun n y hy => ?_) f (h2 k)` and prove the remaining obligations.

Establish `hc : Commute (X.ra τ u) (X.U A m X.I.z ^ (n + 1) - 1)` using `((pb_commU X τ u _).pow_right _).sub_right (Commute.one_right _)`. Rewrite using `[Submodule.mem_comap, ← Module.End.mul_apply, ← hc.eq, Module.End.mul_apply]`. Rewrite `hy` using `[Submodule.mem_comap]`. Introduce `g _ i _`. Rewrite using `[Frame.ra_apply]`.

Simplify using `only [mulVec, dotProduct]`. Conclude with `Submodule.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (hy _ trivial j trivial)`.
-/
private theorem pb_ordMap [IsCNL A] (hθ : X.I.ContChar θ) (u : X.Ub) {U V : Subgroup X.Ub} (f : X.Fn A m)
    (hf : f ∈ X.Ord τ θ U) (h : X.ra τ u f ∈ fixd (X.ra τ) V) : X.ra τ u f ∈ X.Ord τ θ V := by
  refine ⟨⟨(spStab _ _ _ X A m τ θ hθ).2.1 u f hf.1.1, h⟩, ?_⟩
  have h2 := hf.2
  simp only [SetLike.mem_coe, Submodule.mem_iInf] at h2 ⊢
  intro k
  refine pb_iSup _ (fun n y hy => ?_) f (h2 k)
  have hc : Commute (X.ra τ u) (X.U A m X.I.z ^ (n + 1) - 1) :=
    ((pb_commU X τ u _).pow_right _).sub_right (Commute.one_right _)
  rw [Submodule.mem_comap, ← Module.End.mul_apply, ← hc.eq, Module.End.mul_apply]
  rw [Submodule.mem_comap] at hy
  intro g _ i _
  rw [Frame.ra_apply]
  simp only [mulVec, dotProduct]
  exact Submodule.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (hy _ trivial j trivial)

end Fr

section Grp

variable {B C : Type} [Group B] [Group C] (J : B →* C) (UQ : Subgroup C) (hc : ∀ u ∈ UQ, ∀ g, Commute u (J g))
include hc

/- English proof (translation)
Apply the tactic sequence `apply _root_.UpperTheory.Reformulated.B.Qi43.pb_mem <;> assumption`.
-/
private theorem pb_mem (K : Subgroup B) (x : C) : x ∈ UQ ⊔ K.map J ↔ ∃ u ∈ UQ, ∃ k ∈ K, x = u * J k :=
  by apply _root_.UpperTheory.Reformulated.B.Qi43.pb_mem <;> assumption

/- English proof (translation)
Use `⟨fun x hx y => ?_⟩` and prove the remaining obligations. Rewrite `hx`, the goal using `[Subgroup.mem_subgroupOf, pb_mem J UQ hc]`. Take `⟨u', hu', k', hk', e'⟩` from `hx`. Take `⟨u, hu, k, hk, e⟩` from `(pb_mem J UQ hc K _).1 y.2`. Use `⟨u * u' * u⁻¹, mul_mem (mul_mem hu hu') (inv_mem hu), k * k' * k⁻¹, hN.conj_mem ⟨k', hle hk'⟩ hk' ⟨k, hk⟩, ?_⟩` and prove the remaining obligations.

Rewrite using `[Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, e, e', mul_assoc (u * u'), (hc _ (inv_mem hu) _).eq, map_mul, map_mul, map_inv, _root_.mul_inv_rev, mul_assoc u (J k), ← mul_assoc (J k), ← (hc u' hu' k).eq]`. Simplify using `only [mul_assoc]`.
-/
private theorem pb_normal (K K' : Subgroup B) [hN : (K'.subgroupOf K).Normal] (hle : K' ≤ K) :
    ((UQ ⊔ K'.map J).subgroupOf (UQ ⊔ K.map J)).Normal := by
  refine ⟨fun x hx y => ?_⟩
  rw [Subgroup.mem_subgroupOf, pb_mem J UQ hc] at hx ⊢
  obtain ⟨u', hu', k', hk', e'⟩ := hx
  obtain ⟨u, hu, k, hk, e⟩ := (pb_mem J UQ hc K _).1 y.2
  refine ⟨u * u' * u⁻¹, mul_mem (mul_mem hu hu') (inv_mem hu), k * k' * k⁻¹,
    hN.conj_mem ⟨k', hle hk'⟩ hk' ⟨k, hk⟩, ?_⟩
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, e, e', mul_assoc (u * u'), (hc _ (inv_mem hu) _).eq,
    map_mul, map_mul, map_inv, _root_.mul_inv_rev, mul_assoc u (J k), ← mul_assoc (J k), ← (hc u' hu' k).eq]
  simp only [mul_assoc]

/- English proof (translation)
Set `j : K →* (UQ ⊔ K.map J : Subgroup C)` to `(J.comp K.subtype).codRestrict _ fun k => Subgroup.mem_sup_right ⟨k, k.2, rfl⟩`. Set `φ` to `QuotientGroup.map (K'.subgroupOf K) ((UQ ⊔ K'.map J).subgroupOf (UQ ⊔ K.map J)) j fun k hk => Subgroup.mem_sup_right (S := UQ) ⟨k, hk, rfl⟩`. Use `⟨MulEquiv.ofBijective φ ⟨?_, ?_⟩, fun k => rfl⟩` and prove the remaining obligations. Rewrite using `[injective_iff_map_eq_one]`. Introduce `x hx`.

Take `⟨k, rfl⟩` from `QuotientGroup.mk_surjective x`. Conclude with `(QuotientGroup.eq_one_iff _).2 (hinj k k.2 ((QuotientGroup.eq_one_iff (j k)).1 hx))`. Introduce `x`. Take `⟨y, rfl⟩` from `QuotientGroup.mk_surjective x`. Take `⟨u, hu, k, hk, e⟩` from `(pb_mem J UQ hc K _).1 y.2`.

Use `⟨((⟨k, hk⟩ : K) : K ⧸ K'.subgroupOf K), QuotientGroup.eq.2 ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(J k)⁻¹ * y ∈ UQ ⊔ K'.map J`. Rewrite using `[e, (hc u hu k).eq, inv_mul_cancel_left]`. Conclude with `Subgroup.mem_sup_left hu`.
-/
private theorem pb_equiv (K K' : Subgroup B) [(K'.subgroupOf K).Normal]
    [((UQ ⊔ K'.map J).subgroupOf (UQ ⊔ K.map J)).Normal] (hinj : ∀ k ∈ K, J k ∈ UQ ⊔ K'.map J → k ∈ K') :
    ∃ e : (K ⧸ K'.subgroupOf K) ≃* ((UQ ⊔ K.map J : Subgroup C) ⧸ (UQ ⊔ K'.map J).subgroupOf (UQ ⊔ K.map J)),
      ∀ k : K, e (k : K ⧸ K'.subgroupOf K) = (⟨J k, Subgroup.mem_sup_right ⟨k, k.2, rfl⟩⟩ : (UQ ⊔ K.map J : Subgroup C)) := by
  let j : K →* (UQ ⊔ K.map J : Subgroup C) :=
    (J.comp K.subtype).codRestrict _ fun k => Subgroup.mem_sup_right ⟨k, k.2, rfl⟩
  let φ := QuotientGroup.map (K'.subgroupOf K) ((UQ ⊔ K'.map J).subgroupOf (UQ ⊔ K.map J)) j
    fun k hk => Subgroup.mem_sup_right (S := UQ) ⟨k, hk, rfl⟩
  refine ⟨MulEquiv.ofBijective φ ⟨?_, ?_⟩, fun k => rfl⟩
  · rw [injective_iff_map_eq_one]
    intro x hx
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective x
    exact (QuotientGroup.eq_one_iff _).2 (hinj k k.2 ((QuotientGroup.eq_one_iff (j k)).1 hx))
  · intro x
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨u, hu, k, hk, e⟩ := (pb_mem J UQ hc K _).1 y.2
    refine ⟨((⟨k, hk⟩ : K) : K ⧸ K'.subgroupOf K), QuotientGroup.eq.2 ?_⟩
    change (J k)⁻¹ * y ∈ UQ ⊔ K'.map J
    rw [e, (hc u hu k).eq, inv_mul_cancel_left]
    exact Subgroup.mem_sup_left hu

end Grp

section Main

variable {Γ Ga Gp : Type} [Group Γ] [Group Ga] [Group Gp] (X : Frame Γ Ga Gp) {A : Type} [CommRing A] [IsCNL A] {m : ℕ}
  (τ : X.Ub →* GL (Fin m) A) (θ : X.I.T →* Aˣ)

/- English proof (translation)
Establish `hlevle : ∀ K K', κ K' ≤ κ K → lev K' ≤ lev K` using `fun K K' h => by`. Rewrite using `[hlev, hlev]`. Conclude with `sup_le_sup_left (Subgroup.map_mono h) _`. Establish `hYle : ∀ K K', κ K' ≤ κ K → X.Ord τ θ (lev K) ≤ X.Ord τ θ (lev K')` using `fun K K' h f hf => ⟨⟨hf.1.1, fun u hu => hf.1.2 u (hlevle K K' h hu)⟩, hf.2⟩`. Establish `hMle : ∀ K K', κ K' ≤ κ K → MK K ≤ MK K'` using `fun K K' h f hf => by`.

Rewrite `hf`, the goal using `[hMK]`. Conclude with `pb_locMap op a 1 (hYle K K' h) (fun i => Commute.one_left _) f hf`. Establish `hMY : ∀ K, MK K ≤ X.Ord τ θ (lev K)` using `fun K f hf => by`. Rewrite `hf` using `[hMK]`. Conclude with `hf.1`.

Establish `hdir : Directed (· ≤ ·) MK` using `fun K K' => by`. Take `⟨K'', h1, h2⟩` from `hinf K K'`. Conclude with `⟨K'', hMle _ _ h1, hMle _ _ h2⟩`. Establish `hex : ∀ f ∈ ⨆ K, MK K, ∃ K, f ∈ MK K` using `fun f hf => (Submodule.mem_iSup_of_directed _ hdir).1 hf`. Establish `hUQ : ∀ K, UQ ≤ lev K` using `fun K => by rw [hlev]; exact le_sup_left`.

Establish `hJ : ∀ K, ∀ k ∈ κ K, J k ∈ lev K` using `fun K k hk => by rw [hlev]; exact Subgroup.mem_sup_right ⟨k, hk, rfl⟩`. Establish `hfix : ∀ K f, (∀ u ∈ UQ, X.ra τ u f = f) → (∀ k ∈ κ K, X.ra τ (J k) f = f) → f ∈ fixd (X.ra τ) (lev K)`. Introduce `K f h1 h2 x hx`. Rewrite `hx` using `[hlev, pb_mem J UQ hc]`. Take `⟨u, hu, k, hk, rfl⟩` from `hx`.

Rewrite using `[map_mul, Module.End.mul_apply, h2 k hk, h1 u hu]`. Establish `hact : ∀ K K' g, (∀ k ∈ κ K', g⁻¹ * k * g ∈ κ K) → ∀ f ∈ X.Ord τ θ (lev K), X.ra τ (J g) f ∈ X.Ord τ θ (lev K')`. Introduce `K K' g h f hf`. Use `pb_ordMap X τ θ hθ _ f hf (hfix _ _ (fun u hu => ?_) fun k hk => ?_)` and prove the remaining obligations. Rewrite using `[← Module.End.mul_apply, ← map_mul, (hc u hu g).eq, map_mul, Module.End.mul_apply, hf.1.2 u (hUQ K hu)]`.

Use `conv_rhs => rw [← hf.1.2 _ (hJ K _ (h k hk))]`. Rewrite using `[← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul, ← map_mul, ← map_mul, ← mul_assoc, mul_inv_cancel_left]`. Establish `hst : ∀ g, (⨆ K, MK K) ≤ (⨆ K, MK K).comap (X.ra τ (J g))` using `fun g => iSup_le fun K f hf => by`. Take `⟨K', h⟩` from `hconj K g`. Use `Submodule.mem_iSup_of_mem K' ?_` and prove the remaining obligations.

Rewrite `hf`, the goal using `[hMK]`. Conclude with `pb_locMap op a _ (hact K K' g h) (hop g) f hf`. Set `ρ : Representation A B (⨆ K, MK K : Submodule A (X.Fn A m))` to `Representation.subrepresentation ((X.ra τ).comp J) _ hst`. Establish `hρ : ∀ g f, (ρ g f : X.Fn A m) = X.ra τ (J g) f` using `fun _ _ => rfl`. Establish `h1 : ∀ K, ∀ f ∈ fixd ρ (κ K), f.1 ∈ MK K`.

Introduce `K f hf`. Take `⟨K', h⟩` from `hex f.1 f.2`. Take `⟨K'', l1, l2⟩` from `hinf K K'`. Establish `h3` using `hMle _ _ l2 h`. Establish `h4` using `hMY _ h3`.

Rewrite `h3`, the goal using `[hMK]`. Use `haveI := (hY K'').2`. Conclude with `pb_locInf op a (hYle _ _ l1) (hY K).1.1 (hY K'').1.1 _ h3 ⟨⟨h4.1.1, hfix K _ (fun u hu => h4.1.2 u (hUQ _ hu)) fun k hk => congrArg Subtype.val (hf k hk)⟩, h4.2⟩`. Establish `h2 : ∀ K f (hf : f ∈ MK K), (⟨f, Submodule.mem_iSup_of_mem K hf⟩ : (⨆ K, MK K : Submodule A (X.Fn A m))) ∈ fixd ρ (κ K)` using `fun K f hf k hk => Subtype.ext ((hMY K hf).1.2 _ (hJ K k hk))`. Use `⟨ρ, hρ, fun K => le_antisymm ?_ fun f hf => ⟨_, h2 K f hf, rfl⟩, fun f => hex f.1 f.2, ?_⟩` and prove the remaining obligations.

Introduce and unpack `_ ⟨f, hf, rfl⟩`. Conclude with `h1 K f hf`. Introduce `hneat K K' hN hle hinj`. Use `haveI := pb_normal J UQ hc (κ K) (κ K') hle`. Take `⟨e, he⟩` from `pb_equiv J UQ hc (κ K) (κ K') (by rw [← hlev]; exact hinj)`.

Establish `hi : (UQ ⊔ (κ K').map J).relIndex (UQ ⊔ (κ K).map J) ≠ 0`. Use `hidx K K'` as an intermediate fact. Rewrite `this` using `[Subgroup.relIndex, Subgroup.index, Nat.card_congr e.toEquiv]`. Then use the resulting hypothesis. Take `⟨⟨ρ0, hρ0, hP⟩, -⟩` from `ordProj _ _ _ X A m τ θ hθ (UQ ⊔ (κ K).map J) (UQ ⊔ (κ K').map J) (sup_le_sup_left (Subgroup.map_mono hle) _) hi (hlev K ▸ hfin K) (hlev K ▸ hneat K)`. Establish `hρe : ∀ (k : κ K) f, (ρ0 (e (k : κ K ⧸ (κ K').subgroupOf (κ K))) f : X.Fn A m) = X.ra τ (J k) f` using `fun k f => by`.

Rewrite using `[he, hρ0]`. Establish `hMK' : MK K' = locPart (X.Ord τ θ (UQ ⊔ (κ K').map J)) op a` using `by rw [hMK, hlev]`. Establish `hY'` using `hY K'`. Rewrite `hY'` using `[hlev]`. Use `haveI := hY'.2`.

Take `⟨ε, -, hε, hε1, hε2⟩` from `UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.locIdem A _ ι (X.Ord τ θ (UQ ⊔ (κ K').map J)) op a hY'.1`. Establish `hst' : ∀ u : κ K, fixd ρ (κ K') ≤ (fixd ρ (κ K')).comap (ρ u)` using `fun u f hf k hk => by`. Use `hf _ (hN.conj_mem' ⟨k, hle hk⟩ hk u)` as an intermediate fact. Use `conv_rhs => rw [← this]`. Rewrite using `[← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]`.

Simplify using `[mul_assoc]`. Set `ρ1 : Representation A (κ K) (fixd ρ (κ K'))` to `Representation.subrepresentation (ρ.comp (κ K).subtype) _ hst'`. Set `ρ' : Representation A (κ K ⧸ (κ K').subgroupOf (κ K)) (fixd ρ (κ K'))` to `QuotientGroup.lift _ ρ1 fun k hk => LinearMap.ext fun f => Subtype.ext (f.2 k hk)`. Use `⟨ρ', fun _ _ => rfl, ?_⟩` and prove the remaining obligations. Set `i : fixd ρ (κ K') →ₗ[A] X.Ord τ θ (UQ ⊔ (κ K').map J)` to `((Submodule.subtype _).comp (Submodule.subtype _)).codRestrict _ fun f => (hMK' ▸ h1 K' f.1 f.2).1`.

Establish `hεm : ∀ y, (ε y : X.Fn A m) ∈ MK K'` using `fun y => by`. Rewrite using `[hMK', hε1, ← Module.End.mul_apply, hε.eq]`. Set `p : X.Ord τ θ (UQ ⊔ (κ K').map J) →ₗ[A] fixd ρ (κ K')` to `(((Submodule.subtype _).comp ε).codRestrict _ fun y => Submodule.mem_iSup_of_mem K' (hεm y)).codRestrict _ fun y => h2 K' _ (hεm y)`. Use `pb_proj e ρ' ρ0 i p (fun x => Subtype.ext (Subtype.ext ?_)) (fun g x => Subtype.ext ?_) (fun g x => Subtype.ext (Subtype.ext ?_)) hP` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(ε (i x) : X.Fn A m) = (i x : X.Fn A m)`.

Rewrite using `[(hε1 (i x)).1 (hMK' ▸ h1 K' x.1 x.2)]`. Take `⟨k, rfl⟩` from `QuotientGroup.mk_surjective g`. Rewrite using `[hρe]`. Both sides reduce to the same expression. Take `⟨k, rfl⟩` from `QuotientGroup.mk_surjective g`.

Use `hε2 (ρ0 (e (k : κ K ⧸ (κ K').subgroupOf (κ K)))) fun j t ht => LinearMap.ext fun y => Subtype.ext (by` as an intermediate fact. Rewrite using `[Module.End.mul_apply, Module.End.mul_apply, hρe, ht, ht, hρe, ← Module.End.mul_apply, (hop k j).eq, Module.End.mul_apply])`. Express the relevant statement in the definitionally equal form `(ε (ρ0 _ x) : X.Fn A m) = X.ra τ (J k) (ε x)`. Rewrite using `[← hρe, ← Module.End.mul_apply, ← this, Module.End.mul_apply]`.
-/
private theorem pb_main (hθ : X.I.ContChar θ) {B Lev ι : Type} [Group B] [Nonempty Lev] (J : B →* X.Ub) (UQ : Subgroup X.Ub)
    (hc : ∀ u ∈ UQ, ∀ g, Commute u (J g)) (κ : Lev → Subgroup B) (lev : Lev → Subgroup X.Ub)
    (hlev : ∀ K, lev K = UQ ⊔ (κ K).map J) (hinf : ∀ K K', ∃ K'', κ K'' ≤ κ K ∧ κ K'' ≤ κ K')
    (hconj : ∀ K g, ∃ K', ∀ k ∈ κ K', g⁻¹ * k * g ∈ κ K) (hidx : ∀ K K', (κ K').relIndex (κ K) ≠ 0)
    (hfin : ∀ K, X.FinLevel (lev K)) (op : ι → Module.End A (X.Fn A m)) (a : ι → A)
    (hop : ∀ g i, Commute (X.ra τ (J g)) (op i))
    (hY : ∀ K, CommOn (X.Ord τ θ (lev K)) op ∧ Module.Finite A (X.Ord τ θ (lev K)))
    (MK : Lev → Submodule A (X.Fn A m)) (hMK : ∀ K, MK K = locPart (X.Ord τ θ (lev K)) op a) :
    ∃ ρ : Representation A B (⨆ K, MK K : Submodule A (X.Fn A m)), (∀ g f, (ρ g f : X.Fn A m) = X.ra τ (J g) f) ∧
      (∀ K, (fixd ρ (κ K)).map (Submodule.subtype _) = MK K) ∧ (∀ f : (⨆ K, MK K : Submodule A (X.Fn A m)), ∃ K, (f : X.Fn A m) ∈ MK K) ∧
      ((∀ K, X.Neat (lev K)) → ∀ (K K' : Lev) [((κ K').subgroupOf (κ K)).Normal], κ K' ≤ κ K →
        (∀ k ∈ κ K, J k ∈ lev K' → k ∈ κ K') →
        ∃ ρ' : Representation A (κ K ⧸ (κ K').subgroupOf (κ K)) (fixd ρ (κ K')), (∀ (u : κ K) f, (ρ' (u : _ ⧸ _) f).1 = ρ u f) ∧
          Module.Projective (MonoidAlgebra A (κ K ⧸ (κ K').subgroupOf (κ K))) ρ'.asModule) := by
  have hlevle : ∀ K K', κ K' ≤ κ K → lev K' ≤ lev K := fun K K' h => by
    rw [hlev, hlev]
    exact sup_le_sup_left (Subgroup.map_mono h) _
  have hYle : ∀ K K', κ K' ≤ κ K → X.Ord τ θ (lev K) ≤ X.Ord τ θ (lev K') := fun K K' h f hf =>
    ⟨⟨hf.1.1, fun u hu => hf.1.2 u (hlevle K K' h hu)⟩, hf.2⟩
  have hMle : ∀ K K', κ K' ≤ κ K → MK K ≤ MK K' := fun K K' h f hf => by
    rw [hMK] at hf ⊢
    exact pb_locMap op a 1 (hYle K K' h) (fun i => Commute.one_left _) f hf
  have hMY : ∀ K, MK K ≤ X.Ord τ θ (lev K) := fun K f hf => by
    rw [hMK] at hf
    exact hf.1
  have hdir : Directed (· ≤ ·) MK := fun K K' => by
    obtain ⟨K'', h1, h2⟩ := hinf K K'
    exact ⟨K'', hMle _ _ h1, hMle _ _ h2⟩
  have hex : ∀ f ∈ ⨆ K, MK K, ∃ K, f ∈ MK K := fun f hf => (Submodule.mem_iSup_of_directed _ hdir).1 hf
  have hUQ : ∀ K, UQ ≤ lev K := fun K => by rw [hlev]; exact le_sup_left
  have hJ : ∀ K, ∀ k ∈ κ K, J k ∈ lev K := fun K k hk => by rw [hlev]; exact Subgroup.mem_sup_right ⟨k, hk, rfl⟩
  have hfix : ∀ K f, (∀ u ∈ UQ, X.ra τ u f = f) → (∀ k ∈ κ K, X.ra τ (J k) f = f) → f ∈ fixd (X.ra τ) (lev K) := by
    intro K f h1 h2 x hx
    rw [hlev, pb_mem J UQ hc] at hx
    obtain ⟨u, hu, k, hk, rfl⟩ := hx
    rw [map_mul, Module.End.mul_apply, h2 k hk, h1 u hu]
  have hact : ∀ K K' g, (∀ k ∈ κ K', g⁻¹ * k * g ∈ κ K) → ∀ f ∈ X.Ord τ θ (lev K), X.ra τ (J g) f ∈ X.Ord τ θ (lev K') := by
    intro K K' g h f hf
    refine pb_ordMap X τ θ hθ _ f hf (hfix _ _ (fun u hu => ?_) fun k hk => ?_)
    · rw [← Module.End.mul_apply, ← map_mul, (hc u hu g).eq, map_mul, Module.End.mul_apply, hf.1.2 u (hUQ K hu)]
    · conv_rhs => rw [← hf.1.2 _ (hJ K _ (h k hk))]
      rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul, ← map_mul, ← map_mul, ← mul_assoc,
        mul_inv_cancel_left]
  have hst : ∀ g, (⨆ K, MK K) ≤ (⨆ K, MK K).comap (X.ra τ (J g)) := fun g => iSup_le fun K f hf => by
    obtain ⟨K', h⟩ := hconj K g
    refine Submodule.mem_iSup_of_mem K' ?_
    rw [hMK] at hf ⊢
    exact pb_locMap op a _ (hact K K' g h) (hop g) f hf
  let ρ : Representation A B (⨆ K, MK K : Submodule A (X.Fn A m)) :=
    Representation.subrepresentation ((X.ra τ).comp J) _ hst
  have hρ : ∀ g f, (ρ g f : X.Fn A m) = X.ra τ (J g) f := fun _ _ => rfl
  have h1 : ∀ K, ∀ f ∈ fixd ρ (κ K), f.1 ∈ MK K := by
    intro K f hf
    obtain ⟨K', h⟩ := hex f.1 f.2
    obtain ⟨K'', l1, l2⟩ := hinf K K'
    have h3 := hMle _ _ l2 h
    have h4 := hMY _ h3
    rw [hMK] at h3 ⊢
    haveI := (hY K'').2
    exact pb_locInf op a (hYle _ _ l1) (hY K).1.1 (hY K'').1.1 _ h3
      ⟨⟨h4.1.1, hfix K _ (fun u hu => h4.1.2 u (hUQ _ hu)) fun k hk => congrArg Subtype.val (hf k hk)⟩, h4.2⟩
  have h2 : ∀ K f (hf : f ∈ MK K), (⟨f, Submodule.mem_iSup_of_mem K hf⟩ : (⨆ K, MK K : Submodule A (X.Fn A m))) ∈ fixd ρ (κ K) :=
    fun K f hf k hk => Subtype.ext ((hMY K hf).1.2 _ (hJ K k hk))
  refine ⟨ρ, hρ, fun K => le_antisymm ?_ fun f hf => ⟨_, h2 K f hf, rfl⟩, fun f => hex f.1 f.2, ?_⟩
  · rintro _ ⟨f, hf, rfl⟩
    exact h1 K f hf
  intro hneat K K' hN hle hinj
  haveI := pb_normal J UQ hc (κ K) (κ K') hle
  obtain ⟨e, he⟩ := pb_equiv J UQ hc (κ K) (κ K') (by rw [← hlev]; exact hinj)
  have hi : (UQ ⊔ (κ K').map J).relIndex (UQ ⊔ (κ K).map J) ≠ 0 := by
    have := hidx K K'
    rwa [Subgroup.relIndex, Subgroup.index, Nat.card_congr e.toEquiv] at this
  obtain ⟨⟨ρ0, hρ0, hP⟩, -⟩ := ordProj _ _ _ X A m τ θ hθ (UQ ⊔ (κ K).map J) (UQ ⊔ (κ K').map J)
    (sup_le_sup_left (Subgroup.map_mono hle) _) hi (hlev K ▸ hfin K) (hlev K ▸ hneat K)
  have hρe : ∀ (k : κ K) f, (ρ0 (e (k : κ K ⧸ (κ K').subgroupOf (κ K))) f : X.Fn A m) = X.ra τ (J k) f := fun k f => by
    rw [he, hρ0]
  have hMK' : MK K' = locPart (X.Ord τ θ (UQ ⊔ (κ K').map J)) op a := by rw [hMK, hlev]
  have hY' := hY K'
  rw [hlev] at hY'
  haveI := hY'.2
  obtain ⟨ε, -, hε, hε1, hε2⟩ := UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.locIdem A _ ι (X.Ord τ θ (UQ ⊔ (κ K').map J)) op a hY'.1
  have hst' : ∀ u : κ K, fixd ρ (κ K') ≤ (fixd ρ (κ K')).comap (ρ u) := fun u f hf k hk => by
    have := hf _ (hN.conj_mem' ⟨k, hle hk⟩ hk u)
    conv_rhs => rw [← this]
    rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
    simp [mul_assoc]
  let ρ1 : Representation A (κ K) (fixd ρ (κ K')) := Representation.subrepresentation (ρ.comp (κ K).subtype) _ hst'
  let ρ' : Representation A (κ K ⧸ (κ K').subgroupOf (κ K)) (fixd ρ (κ K')) :=
    QuotientGroup.lift _ ρ1 fun k hk => LinearMap.ext fun f => Subtype.ext (f.2 k hk)
  refine ⟨ρ', fun _ _ => rfl, ?_⟩
  let i : fixd ρ (κ K') →ₗ[A] X.Ord τ θ (UQ ⊔ (κ K').map J) :=
    ((Submodule.subtype _).comp (Submodule.subtype _)).codRestrict _ fun f => (hMK' ▸ h1 K' f.1 f.2).1
  have hεm : ∀ y, (ε y : X.Fn A m) ∈ MK K' := fun y => by
    rw [hMK', hε1, ← Module.End.mul_apply, hε.eq]
  let p : X.Ord τ θ (UQ ⊔ (κ K').map J) →ₗ[A] fixd ρ (κ K') :=
    (((Submodule.subtype _).comp ε).codRestrict _ fun y => Submodule.mem_iSup_of_mem K' (hεm y)).codRestrict _
      fun y => h2 K' _ (hεm y)
  refine pb_proj e ρ' ρ0 i p (fun x => Subtype.ext (Subtype.ext ?_)) (fun g x => Subtype.ext ?_)
    (fun g x => Subtype.ext (Subtype.ext ?_)) hP
  · change (ε (i x) : X.Fn A m) = (i x : X.Fn A m)
    rw [(hε1 (i x)).1 (hMK' ▸ h1 K' x.1 x.2)]
  · obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective g
    rw [hρe]
    rfl
  · obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective g
    have := hε2 (ρ0 (e (k : κ K ⧸ (κ K').subgroupOf (κ K)))) fun j t ht => LinearMap.ext fun y => Subtype.ext (by
      rw [Module.End.mul_apply, Module.End.mul_apply, hρe, ht, ht, hρe, ← Module.End.mul_apply, (hop k j).eq,
        Module.End.mul_apply])
    change (ε (ρ0 _ x) : X.Fn A m) = X.ra τ (J k) (ε x)
    rw [← hρe, ← Module.End.mul_apply, ← this, Module.End.mul_apply]

end Main

/- English proof (translation)
Use `haveI : CompactSpace K := isCompact_iff_compactSpace.1 hK`. Use `haveI : DiscreteTopology (K ⧸ K'.subgroupOf K) := QuotientGroup.discreteTopology (hK'.preimage continuous_subtype_val)`. Use `haveI : Finite (K ⧸ K'.subgroupOf K) := finite_of_compact_of_discrete`. Conclude with `Subgroup.index_ne_zero_of_finite`.
-/
private theorem pb_idx {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {K K' : Subgroup G}
    (hK : IsCompact (K : Set G)) (hK' : IsOpen (K' : Set G)) : K'.relIndex K ≠ 0 := by
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 hK
  haveI : DiscreteTopology (K ⧸ K'.subgroupOf K) := QuotientGroup.discreteTopology (hK'.preimage continuous_subtype_val)
  haveI : Finite (K ⧸ K'.subgroupOf K) := finite_of_compact_of_discrete
  exact Subgroup.index_ne_zero_of_finite

section Top

variable {Q : Type} [Fintype Q] [DecidableEq Q] {G : Q → Type} [∀ q, Group (G q)] [∀ q, TopologicalSpace (G q)]
  [∀ q, IsTopologicalGroup (G q)]

omit [Fintype Q] [DecidableEq Q] in
/- English proof (translation)
Assemble the required witnesses or components as `⟨⟨fun q => K.1 q ⊓ K'.1 q, fun q => ⟨(K.2 q).1.inter (K'.2 q).1, (K.2 q).2.inter_right ((K'.1 q).isClosed_of_isOpen (K'.2 q).1)⟩⟩, fun _ hk q hq => (hk q hq).1, fun _ hk q hq => (hk q hq).2⟩`.
-/
private theorem pb_inf (K K' : {K : ∀ q, Subgroup (G q) // ∀ q, IsOpen (K q : Set (G q)) ∧ IsCompact (K q : Set (G q))}) :
    ∃ K'' : {K : ∀ q, Subgroup (G q) // ∀ q, IsOpen (K q : Set (G q)) ∧ IsCompact (K q : Set (G q))},
      Subgroup.pi Set.univ K''.1 ≤ Subgroup.pi Set.univ K.1 ∧ Subgroup.pi Set.univ K''.1 ≤ Subgroup.pi Set.univ K'.1 :=
  ⟨⟨fun q => K.1 q ⊓ K'.1 q, fun q => ⟨(K.2 q).1.inter (K'.2 q).1,
      (K.2 q).2.inter_right ((K'.1 q).isClosed_of_isOpen (K'.2 q).1)⟩⟩,
    fun _ hk q hq => (hk q hq).1, fun _ hk q hq => (hk q hq).2⟩

omit [Fintype Q] [DecidableEq Q] in
/- English proof (translation)
Assemble the required witnesses or components as `⟨⟨fun q => (K.1 q).comap (MulAut.conj (g q)⁻¹).toMonoidHom, fun q => by let e := (Homeomorph.mulLeft (g q)⁻¹).trans (Homeomorph.mulRight (g q)⁻¹⁻¹) exact ⟨(K.2 q).1.preimage e.continuous, e.isCompact_preimage.2 (K.2 q).2⟩⟩, fun k hk q hq => by simpa using hk q hq⟩`.
-/
private theorem pb_conj (K : {K : ∀ q, Subgroup (G q) // ∀ q, IsOpen (K q : Set (G q)) ∧ IsCompact (K q : Set (G q))})
    (g : ∀ q, G q) : ∃ K' : {K : ∀ q, Subgroup (G q) // ∀ q, IsOpen (K q : Set (G q)) ∧ IsCompact (K q : Set (G q))},
      ∀ k ∈ Subgroup.pi Set.univ K'.1, g⁻¹ * k * g ∈ Subgroup.pi Set.univ K.1 :=
  ⟨⟨fun q => (K.1 q).comap (MulAut.conj (g q)⁻¹).toMonoidHom, fun q => by
      let e := (Homeomorph.mulLeft (g q)⁻¹).trans (Homeomorph.mulRight (g q)⁻¹⁻¹)
      exact ⟨(K.2 q).1.preimage e.continuous, e.isCompact_preimage.2 (K.2 q).2⟩⟩,
    fun k hk q hq => by simpa using hk q hq⟩

omit [DecidableEq Q] in
/- English proof (translation)
Use `pb_idx ?_ ?_` and prove the remaining obligations. Rewrite using `[Subgroup.coe_pi]`. Conclude with `isCompact_univ_pi fun q => (K.2 q).2`. Rewrite using `[Subgroup.coe_pi]`. Conclude with `isOpen_set_pi Set.finite_univ fun q _ => (K'.2 q).1`.
-/
private theorem pb_idx' (K K' : {K : ∀ q, Subgroup (G q) // ∀ q, IsOpen (K q : Set (G q)) ∧ IsCompact (K q : Set (G q))}) :
    (Subgroup.pi Set.univ K'.1).relIndex (Subgroup.pi Set.univ K.1) ≠ 0 := by
  refine pb_idx ?_ ?_
  · rw [Subgroup.coe_pi]
    exact isCompact_univ_pi fun q => (K.2 q).2
  · rw [Subgroup.coe_pi]
    exact isOpen_set_pi Set.finite_univ fun q _ => (K'.2 q).1

omit [∀ q, TopologicalSpace (G q)] [∀ q, IsTopologicalGroup (G q)] in
/- English proof (translation)
Set `J : (∀ q, G q) →* C` to `MonoidHom.noncommPiCoprod s fun q q' hq => h q q' hq`. Establish `hJ : ∀ q g, J (Pi.mulSingle q g) = s q g` using `fun q g => MonoidHom.noncommPiCoprod_mulSingle _ q g`. Use `⟨J, hJ, fun u hu g => ?_, fun K => ?_⟩` and prove the remaining obligations. Simplify using `only [J, MonoidHom.noncommPiCoprod_apply]`. Conclude with `Finset.noncommProd_commute _ _ (fun q _ q' _ hq => h q q' hq _ _) _ fun q _ => hu q _`.

Use `le_antisymm (iSup_le fun q => ?_) ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨g, hg, rfl⟩`. Conclude with `⟨Pi.mulSingle q g, (Subgroup.mulSingle_mem_pi _ _).2 fun _ => hg, hJ q g⟩`. Introduce and unpack `_ ⟨g, hg, rfl⟩`. Simplify using `only [J, MonoidHom.noncommPiCoprod_apply]`.

Conclude with `Subgroup.noncommProd_mem _ (fun q _ q' _ hq => h q q' hq _ _) fun q _ => Subgroup.mem_iSup_of_mem q ⟨g q, hg q trivial, rfl⟩`.
-/
private theorem pb_J {C : Type} [Group C] (s : ∀ q, G q →* C) (h : ∀ q q', q ≠ q' → ∀ g g', Commute (s q g) (s q' g')) :
    ∃ J : (∀ q, G q) →* C, (∀ q g, J (Pi.mulSingle q g) = s q g) ∧
      (∀ u, (∀ q g, Commute u (s q g)) → ∀ g, Commute u (J g)) ∧
      ∀ K : ∀ q, Subgroup (G q), ⨆ q, (K q).map (s q) = (Subgroup.pi Set.univ K).map J := by
  let J : (∀ q, G q) →* C := MonoidHom.noncommPiCoprod s fun q q' hq => h q q' hq
  have hJ : ∀ q g, J (Pi.mulSingle q g) = s q g := fun q g => MonoidHom.noncommPiCoprod_mulSingle _ q g
  refine ⟨J, hJ, fun u hu g => ?_, fun K => ?_⟩
  · simp only [J, MonoidHom.noncommPiCoprod_apply]
    exact Finset.noncommProd_commute _ _ (fun q _ q' _ hq => h q q' hq _ _) _ fun q _ => hu q _
  refine le_antisymm (iSup_le fun q => ?_) ?_
  · rintro _ ⟨g, hg, rfl⟩
    exact ⟨Pi.mulSingle q g, (Subgroup.mulSingle_mem_pi _ _).2 fun _ => hg, hJ q g⟩
  · rintro _ ⟨g, hg, rfl⟩
    simp only [J, MonoidHom.noncommPiCoprod_apply]
    exact Subgroup.noncommProd_mem _ (fun q _ q' _ hq => h q q' hq _ _) fun q _ => Subgroup.mem_iSup_of_mem q ⟨g q, hg q trivial, rfl⟩

end Top

/- English proof (translation)
The claim follows from `finsum_induction (fun t => Commute (ρ u) t) (Commute.zero_right _) (fun _ _ => Commute.add_right) fun _ => (h _).map ρ`.
-/
private theorem pb_dc {A H H' M : Type} [CommRing A] [Group H] [Group H'] [AddCommGroup M] [Module A M]
    (ρ : Representation A H M) (s : H' →* H) (u : H) (h : ∀ g, Commute u (s g)) (K K' : Subgroup H') (x : H') :
    Commute (ρ u) (dc (ρ.comp s) K K' x) :=
  finsum_induction (fun t => Commute (ρ u) t) (Commute.zero_right _) (fun _ _ => Commute.add_right) fun _ => (h _).map ρ

end Helpers

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V UpperTheory.V.Hi
open UpperTheory.V.HV (Coef)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000

/- English proof (translation)
Introduce `L Ω _ _ _ _ _ l _ n c H hH A _ _ _ θ hθ a _`. Use `haveI : Finite (ResidueField c.O) := Module.finite_of_finite (ResidueField ℤ_[l])`. Use `haveI : IsCNL A := IsCNL.ofCO c.O A`. Use `haveI : Nonempty H.Lev := ⟨⟨fun q => KO _ (Fin n), fun q => ⟨GlobalTheory.SplitFlip.isOpen_KO, GlobalTheory.SplitFlip.isCompact_KO⟩⟩⟩`. Take `⟨J, hJ, hcm, hK⟩` from `pb_J (fun q => H.sec (H.wq q)) hH.Q_Q`.

Establish `hlev : ∀ K : H.Lev, H.lev K = H.UQ ⊔ (Subgroup.pi Set.univ K.1).map J` using `fun K => congrArg (H.UQ ⊔ ·) (hK K.1)`. Establish `hcomm` using `hiComm L Ω l n c H hH A θ hθ`. Establish `hop : ∀ g i, Commute (H.X.ra (H.τA A) (J g)) (H.op A i)`. Introduce and unpack `g (x | x)`. Conclude with `pb_dc _ _ _ (fun g' => (hcm _ (fun q' g'' => (hH.sectionsCommuteAtSplit q' _ x.1.2 g'' g').symm) g).symm) _ _ _`.

Conclude with `pb_commU _ _ _ _`. Take `⟨ρ, h1, h2, h3, h4⟩` from `pb_main H.X (H.τA A) θ hθ.cont J H.UQ (fun u hu => hcm u fun q => hH.Q_UQ q u hu) (fun K : H.Lev => Subgroup.pi Set.univ K.1) H.lev hlev pb_inf pb_conj pb_idx' hH.fin (H.op A) (fun i => algebraMap c.O A (a i)) hop (fun K => ⟨(hcomm K).1, (hcomm K).2.1⟩) (H.MK θ a) fun _ => rfl`. Use `⟨ρ, fun q g f => (h1 _ f).trans (congrArg (fun u => H.X.ra (H.τA A) u f) (hJ q g)), h2, h3, fun hn K K' _ hle hinj => ?_⟩` and prove the remaining obligations. Conclude with `h4 hn K K' (fun k hk q hq => hle q (hk q hq)) fun k hk => hinj k hk J hJ`.
-/
theorem UpperTheory.V.Hi.piBasic :
    ∀ (L Ω : Type) [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (l : ℕ) [Fact l.Prime] (n : ℕ) (c : Coef l) (H : HSet L Ω l n c), H.Ax →
    ∀ (A : Type) [CommRing A] [Algebra c.O A] [Alg.IsCO c.O A] (θ : H.X.I.T →* Aˣ), H.IsWt θ →
    ∀ (a : H.Op → c.O) [DecidableEq H.Q], ∃ ρ : Representation A (GV n H.wq) (⨆ K, H.MK θ a K : Submodule A (H.X.Fn A H.m)), (∀ q g f, (ρ (Pi.mulSingle q g) f : H.X.Fn A H.m) = H.X.ra (H.τA A) (H.sec (H.wq q) g) f) ∧ (∀ K : H.Lev, (fixd ρ (Subgroup.pi Set.univ K.1)).map (Submodule.subtype _) = H.MK θ a K) ∧ (∀ f : (⨆ K, H.MK θ a K : Submodule A (H.X.Fn A H.m)), ∃ K, (f : H.X.Fn A H.m) ∈ H.MK θ a K) ∧ ((∀ K, H.X.Neat (H.lev K)) → ∀ (K K' : H.Lev) [((Subgroup.pi Set.univ K'.1).subgroupOf (Subgroup.pi Set.univ K.1)).Normal], (∀ q, K'.1 q ≤ K.1 q) → (∀ k ∈ Subgroup.pi Set.univ K.1, ∀ j : GV n H.wq →* H.X.Ub, (∀ q g, j (Pi.mulSingle q g) = H.sec (H.wq q) g) → j k ∈ H.lev K' → k ∈ Subgroup.pi Set.univ K'.1) → ∃ ρ' : Representation A (Subgroup.pi Set.univ K.1 ⧸ (Subgroup.pi Set.univ K'.1).subgroupOf (Subgroup.pi Set.univ K.1)) (fixd ρ (Subgroup.pi Set.univ K'.1)), (∀ (u : Subgroup.pi Set.univ K.1) f, (ρ' (u : _ ⧸ _) f).1 = ρ u f) ∧ Module.Projective (MonoidAlgebra A (Subgroup.pi Set.univ K.1 ⧸ (Subgroup.pi Set.univ K'.1).subgroupOf (Subgroup.pi Set.univ K.1))) ρ'.asModule) := by
  intro L Ω _ _ _ _ _ l _ n c H hH A _ _ _ θ hθ a _
  haveI : Finite (ResidueField c.O) := Module.finite_of_finite (ResidueField ℤ_[l])
  haveI : IsCNL A := IsCNL.ofCO c.O A
  haveI : Nonempty H.Lev := ⟨⟨fun q => KO _ (Fin n), fun q => ⟨GlobalTheory.SplitFlip.isOpen_KO, GlobalTheory.SplitFlip.isCompact_KO⟩⟩⟩
  obtain ⟨J, hJ, hcm, hK⟩ := pb_J (fun q => H.sec (H.wq q)) hH.Q_Q
  have hlev : ∀ K : H.Lev, H.lev K = H.UQ ⊔ (Subgroup.pi Set.univ K.1).map J := fun K => congrArg (H.UQ ⊔ ·) (hK K.1)
  have hcomm := hiComm L Ω l n c H hH A θ hθ
  have hop : ∀ g i, Commute (H.X.ra (H.τA A) (J g)) (H.op A i) := by
    rintro g (x | x)
    · exact pb_dc _ _ _ (fun g' => (hcm _ (fun q' g'' => (hH.sectionsCommuteAtSplit q' _ x.1.2 g'' g').symm) g).symm) _ _ _
    · exact pb_commU _ _ _ _
  obtain ⟨ρ, h1, h2, h3, h4⟩ := pb_main H.X (H.τA A) θ hθ.cont J H.UQ (fun u hu => hcm u fun q => hH.Q_UQ q u hu)
    (fun K : H.Lev => Subgroup.pi Set.univ K.1) H.lev hlev pb_inf pb_conj pb_idx' hH.fin (H.op A)
    (fun i => algebraMap c.O A (a i)) hop (fun K => ⟨(hcomm K).1, (hcomm K).2.1⟩) (H.MK θ a) fun _ => rfl
  refine ⟨ρ, fun q g f => (h1 _ f).trans (congrArg (fun u => H.X.ra (H.τA A) u f) (hJ q g)), h2, h3, fun hn K K' _ hle hinj => ?_⟩
  exact h4 hn K K' (fun k hk q hq => hle q (hk q hq)) fun k hk => hinj k hk J hJ
