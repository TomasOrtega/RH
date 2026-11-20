import Mathlib

noncomputable section

open Filter

namespace UpperTheory.V.AlgebraTools

variable (l : ℕ) (G : Type) [Group G] [TopologicalSpace G]

def IsProL : Prop := ∀ N : OpenNormalSubgroup G, IsPGroup l (G ⧸ N.toSubgroup)

/- English proof (translation)
Unfold `IsProL`. Use `forall_congr' fun N => ?_` and prove the remaining obligations. Prove the components needed by the constructor for the conclusion. Introduce `h g`. Take `⟨k, hk⟩` from `h (g : G ⧸ N.toSubgroup)`.

Conclude with `⟨k, by rwa [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at hk⟩`. Introduce `h x`. Take `⟨g, rfl⟩` from `QuotientGroup.mk_surjective x`. Take `⟨k, hk⟩` from `h g`. Conclude with `⟨k, by rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]; exact hk⟩`.
-/
theorem isProL_iff : IsProL l G ↔ ∀ (N : OpenNormalSubgroup G) (g : G), ∃ k : ℕ, g ^ l ^ k ∈ N.toSubgroup := by
  unfold IsProL
  refine forall_congr' fun N => ?_
  constructor
  · intro h g
    obtain ⟨k, hk⟩ := h (g : G ⧸ N.toSubgroup)
    exact ⟨k, by rwa [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at hk⟩
  · intro h x
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨k, hk⟩ := h g
    exact ⟨k, by rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]; exact hk⟩

def proLRes : Subgroup G :=
  ⨅ N : {N : OpenNormalSubgroup G // IsPGroup l (G ⧸ N.toSubgroup)}, N.1.toSubgroup

variable {l G} in
/- English proof (translation)
Simplify using `only [proLRes, Subgroup.mem_iInf, Subtype.forall]`.
-/
theorem mem_proLRes {g : G} :
    g ∈ proLRes l G ↔ ∀ N : OpenNormalSubgroup G, IsPGroup l (G ⧸ N.toSubgroup) → g ∈ N.toSubgroup := by
  simp only [proLRes, Subgroup.mem_iInf, Subtype.forall]

instance : (proLRes l G).Normal :=
  ⟨fun _ h g => mem_proLRes.2 fun N hN => N.isNormal'.conj_mem _ (mem_proLRes.1 h N hN) g⟩

/- English proof (translation)
Rewrite using `[proLRes, Subgroup.coe_iInf]`. Conclude with `isClosed_iInter fun N => N.1.toOpenSubgroup.isClosed`.
-/
theorem isClosed_proLRes [ContinuousMul G] : IsClosed (proLRes l G : Set G) := by
  rw [proLRes, Subgroup.coe_iInf]
  exact isClosed_iInter fun N => N.1.toOpenSubgroup.isClosed

variable {G} in

def proLResOf (H : Subgroup G) : Subgroup G := (proLRes l H).map H.subtype

variable {G} in

def TopGen (s : Set G) : Prop := Dense (Subgroup.closure s : Set G)

def TopFG : Prop := ∃ s : Set G, s.Finite ∧ TopGen s

variable {G} in
/- English proof (translation)
Rewrite using `[TopGen, dense_iff_closure_eq, ← Subgroup.topologicalClosure_coe, ← Subgroup.coe_top, SetLike.coe_set_eq]`.
-/
theorem topGen_iff [IsTopologicalGroup G] (s : Set G) :
    TopGen s ↔ (Subgroup.closure s).topologicalClosure = ⊤ := by
  rw [TopGen, dense_iff_closure_eq, ← Subgroup.topologicalClosure_coe, ← Subgroup.coe_top,
    SetLike.coe_set_eq]

variable {G} in

def limKer {ι : Type} (F : Filter ι) (K : ι → Subgroup G) : Subgroup G where
  carrier := {g | ∀ O : OpenNormalSubgroup G, ∀ᶠ i in F, g ∈ K i ⊔ O.toSubgroup}
  mul_mem' ha hb O := ((ha O).and (hb O)).mono fun _ h => mul_mem h.1 h.2
  one_mem' _ := Eventually.of_forall fun _ => one_mem _
  inv_mem' h O := (h O).mono fun _ h => inv_mem h

variable {G} in
/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem mem_limKer {ι : Type} {F : Filter ι} {K : ι → Subgroup G} {g : G} :
    g ∈ limKer F K ↔ ∀ O : OpenNormalSubgroup G, ∀ᶠ i in F, g ∈ K i ⊔ O.toSubgroup := Iff.rfl

variable {G} in
instance limKer_normal {ι : Type} (F : Filter ι) (K : ι → Subgroup G) [∀ i, (K i).Normal] :
    (limKer F K).Normal :=
  ⟨fun _ h g O => (h O).mono fun i hi => by
    haveI := O.isNormal'
    exact (Subgroup.sup_normal (K i) O.toSubgroup).conj_mem _ hi g⟩

end UpperTheory.V.AlgebraTools
