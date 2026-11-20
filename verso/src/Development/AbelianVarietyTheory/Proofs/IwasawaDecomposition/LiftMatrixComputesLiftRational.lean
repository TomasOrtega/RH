import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMtTieCoord
import Formalism.LocalToGlobal.Divisibility.RowSideTie

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.DivisionValues
open Formalism.IndefR.Cx
open scoped InnerProductSpace Matrix

namespace GlobalTheory.Mem.LiftTheta

section Core

variable {K : Type} [Field K] [NumberField K] {σ : K →+* ℂ} {N H : Type} [AddCommGroup N] [Module ℂ N] [AddCommGroup H] [Module ℂ H]

omit [NumberField K] in
/- English proof (translation)
Establish `hz : y = ∑ k, y k • (Pi.single k 1 : Fin d → K)`. Use extensionality with `i`. Simplify using `[Pi.single_apply]`. Use `conv_lhs => rw [hz]`. Simplify using `only [map_sum, map_smulₛₗ]`.
-/
theorem semi_expand {d : ℕ} (w : (Fin d → K) →ₛₗ[σ] H) (y : Fin d → K) : w y = ∑ k, σ (y k) • w (Pi.single k 1) := by
  have hz : y = ∑ k, y k • (Pi.single k 1 : Fin d → K) := by
    ext i; simp [Pi.single_apply]
  conv_lhs => rw [hz]
  simp only [map_sum, map_smulₛₗ]

omit [NumberField K] in
/- English proof (translation)
Rewrite using `[injective_iff_map_eq_zero]`. Introduce `y hy`. Rewrite `hy` using `[semi_expand]`. Use function extensionality and compare the values at `k`. Conclude with `(map_eq_zero σ).1 (Fintype.linearIndependent_iff.1 hli _ hy k)`.
-/
theorem semi_injective {d : ℕ} (w : (Fin d → K) →ₛₗ[σ] H) (hli : LinearIndependent ℂ fun k => w (Pi.single k 1)) :
    Function.Injective w := by
  rw [injective_iff_map_eq_zero]
  intro y hy
  rw [semi_expand] at hy
  funext k
  exact (map_eq_zero σ).1 (Fintype.linearIndependent_iff.1 hli _ hy k)

omit [NumberField K] in

/- English proof (translation)
Establish `hex : ∀ y, ∃ n, e n = w y`. Introduce `y`. Establish `: w y ∈ LinearMap.range e`. Rewrite using `[← hsp, semi_expand]`. Conclude with `Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)`.

Conclude with `this`. Use `choose g hg using hex`. Set `j : (Fin d → K) →ₛₗ[σ] N` to `{ toFun := g map_add' := fun x y => he (by simp only [map_add, hg]) map_smul' := fun a x => he (by simp only [map_smulₛₗ, hg, RingHom.id_apply]) }`. Establish `hj : ∀ y, e (j y) = w y` using `hg`. Use `⟨j, hj, LinearIndependent.of_comp e ?_, ?_⟩` and prove the remaining obligations.

Establish `: (e ∘ fun k => j (Pi.single k 1)) = fun k => w (Pi.single k 1)` using `funext fun k => hj _`. Rewrite using `[this]`. Conclude with `hli`. Apply `Submodule.map_injective_of_injective he` to reduce the goal to its premises. Rewrite using `[Submodule.map_top, ← hsp, Submodule.map_span, ← Set.range_comp]`.

Use `congr 2`. Conclude with `funext fun k => hj _`.
-/
theorem exists_form {d : ℕ} (e : N →ₗ[ℂ] H) (he : Function.Injective e) (w : (Fin d → K) →ₛₗ[σ] H)
    (hli : LinearIndependent ℂ fun k => w (Pi.single k 1))
    (hsp : Submodule.span ℂ (Set.range fun k => w (Pi.single k 1)) = LinearMap.range e) :
    ∃ j : (Fin d → K) →ₛₗ[σ] N, (∀ y, e (j y) = w y) ∧ (LinearIndependent ℂ fun k => j (Pi.single k 1)) ∧
      Submodule.span ℂ (Set.range fun k => j (Pi.single k 1)) = ⊤ := by
  have hex : ∀ y, ∃ n, e n = w y := by
    intro y
    have : w y ∈ LinearMap.range e := by
      rw [← hsp, semi_expand]
      exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
    exact this
  choose g hg using hex
  let j : (Fin d → K) →ₛₗ[σ] N :=
    { toFun := g
      map_add' := fun x y => he (by simp only [map_add, hg])
      map_smul' := fun a x => he (by simp only [map_smulₛₗ, hg, RingHom.id_apply]) }
  have hj : ∀ y, e (j y) = w y := hg
  refine ⟨j, hj, LinearIndependent.of_comp e ?_, ?_⟩
  · have : (e ∘ fun k => j (Pi.single k 1)) = fun k => w (Pi.single k 1) := funext fun k => hj _
    rw [this]; exact hli
  · apply Submodule.map_injective_of_injective he
    rw [Submodule.map_top, ← hsp, Submodule.map_span, ← Set.range_comp]
    congr 2
    exact funext fun k => hj _

/- English proof (translation)
Establish `hR : ∀ y, y ∈ AddSubgroup.closure {y | ∃ a : 𝓞 K, ∃ x ∈ S, y = σ (a : K) • x} ↔ ∃ x ∈ L, e (j x) = y`. Introduce `y`. Use `⟨fun hy => ?_, fun hy => AddSubgroup.subset_closure ⟨1, y, (hS y).2 hy, by simp⟩⟩` and prove the remaining obligations. Proceed by induction on `hy using AddSubgroup.closure_induction with`. Consider the case `mem y hy`.

Take `⟨a, u, hu, rfl⟩` from `hy`. Take `⟨x, hx, rfl⟩` from `(hS u).1 hu`. Use `⟨a • x, L.smul_mem a hx, ?_⟩` and prove the remaining obligations. Rewrite using `[← algebraMap_smul K a x, map_smulₛₗ, map_smul]`. Consider the case `zero => exact ⟨0, L.zero_mem, by simp⟩`.

Consider the case `add _ _ _ _ h1 h2`. Take `⟨x, hx, rfl⟩` from `h1`. Take `⟨x', hx', rfl⟩` from `h2`. Conclude with `⟨x + x', L.add_mem hx hx', by simp⟩`. Consider the case `neg _ _ h1`.

Take `⟨x, hx, rfl⟩` from `h1`. Conclude with `⟨-x, L.neg_mem hx, by simp⟩`. Establish `hgen : ∀ v ∈ M.gen, v ∈ M.carrier`. Introduce `v hv`. Use `⟨fun u => if u = v then 1 else 0, ?_⟩` and prove the remaining obligations.

Rewrite using `[Finset.sum_eq_single v]`. Simplify using the standard rewrite rules. Introduce `u _ hu`. Simplify using `[hu]`. Introduce `h`.

Conclude with `absurd hv h`. Establish `hL : ∀ y, y ∈ AddSubgroup.closure {y | ∃ a : 𝓞 K, ∃ x ∈ e '' M.carrier, y = σ (a : K) • x} ↔ ∃ c : N → 𝓞 K, y = e (∑ v ∈ M.gen, σ (c v : K) • v)`. Introduce `y`. Prove the components needed by the constructor for the conclusion. Introduce `hy`.

Proceed by induction on `hy using AddSubgroup.closure_induction with`. Consider the case `mem y hy`. Take `⟨a, _, ⟨_, ⟨c, rfl⟩, rfl⟩, rfl⟩` from `hy`. Use `choose b hb using hφ`. Use `⟨fun v => a * b (c v), ?_⟩` and prove the remaining obligations.

Rewrite using `[← map_smul, Finset.smul_sum]`. Simplify using `[hb, mul_smul]`. Consider the case `zero => exact ⟨0, by simp⟩`. Consider the case `add _ _ _ _ h1 h2`. Take `⟨c, rfl⟩` from `h1`.

Take `⟨c', rfl⟩` from `h2`. Use `⟨c + c', ?_⟩` and prove the remaining obligations. Rewrite using `[← map_add, ← Finset.sum_add_distrib]`. Simplify using `[add_smul]`. Consider the case `neg _ _ h1`.

Take `⟨c, rfl⟩` from `h1`. Use `⟨-c, ?_⟩` and prove the remaining obligations. Rewrite using `[← map_neg, ← Finset.sum_neg_distrib]`. Simplify using the standard rewrite rules. Introduce and unpack `⟨c, rfl⟩`.

Rewrite using `[map_sum]`. Use `AddSubgroup.sum_mem _ fun v hv => AddSubgroup.subset_closure ⟨c v, e v, ⟨v, hgen v hv, rfl⟩, map_smul _ _ _⟩` and prove the remaining obligations. Use `⟨fun v hv => ?_, fun x => ⟨fun hx => ?_, ?_⟩⟩` and prove the remaining obligations. Establish `h1 : e v ∈ AddSubgroup.closure {y | ∃ a : 𝓞 K, ∃ x ∈ e '' M.carrier, y = σ (a : K) • x}` using `AddSubgroup.subset_closure ⟨1, e v, ⟨v, hgen v hv, rfl⟩, by simp⟩`. Rewrite `h1` using `[h, hR]`.

Take `⟨x, -, hx⟩` from `h1`. Conclude with `⟨x, he hx⟩`. Establish `h1` using `(hR _).2 ⟨x, hx, rfl⟩`. Rewrite `h1` using `[← h, hL]`. Take `⟨c, hc⟩` from `h1`.

Conclude with `⟨c, he hc⟩`. Introduce and unpack `⟨c, hc⟩`. Establish `h1` using `(hL (e (j x))).2 ⟨c, congrArg e hc⟩`. Rewrite `h1` using `[h, hR]`. Take `⟨x', hx', hxx⟩` from `h1`.

Rewrite using `[← hj (he hxx)]` and apply the resulting hypothesis.
-/
theorem oLatTie_of_closure {O : Type} [CommRing O] {φ : O →+* ℂ} (hφ : ∀ a, ∃ b : 𝓞 K, φ a = σ (b : K))
    (M : Rows.OLat O φ N) {d : ℕ} (e : N →ₗ[ℂ] H) (he : Function.Injective e) (j : (Fin d → K) →ₛₗ[σ] N)
    (hj : Function.Injective j) (L : Submodule (𝓞 K) (Fin d → K)) (S : Set H) (hS : ∀ y, y ∈ S ↔ ∃ x ∈ L, e (j x) = y)
    (h : AddSubgroup.closure {y | ∃ a : 𝓞 K, ∃ x ∈ e '' M.carrier, y = σ (a : K) • x} =
      AddSubgroup.closure {y | ∃ a : 𝓞 K, ∃ x ∈ S, y = σ (a : K) • x}) :
    OLatTie σ M j L := by
  classical
  have hR : ∀ y, y ∈ AddSubgroup.closure {y | ∃ a : 𝓞 K, ∃ x ∈ S, y = σ (a : K) • x} ↔ ∃ x ∈ L, e (j x) = y := by
    intro y
    refine ⟨fun hy => ?_, fun hy => AddSubgroup.subset_closure ⟨1, y, (hS y).2 hy, by simp⟩⟩
    induction hy using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨a, u, hu, rfl⟩ := hy
      obtain ⟨x, hx, rfl⟩ := (hS u).1 hu
      refine ⟨a • x, L.smul_mem a hx, ?_⟩
      rw [← algebraMap_smul K a x, map_smulₛₗ, map_smul]
    | zero => exact ⟨0, L.zero_mem, by simp⟩
    | add _ _ _ _ h1 h2 =>
      obtain ⟨x, hx, rfl⟩ := h1
      obtain ⟨x', hx', rfl⟩ := h2
      exact ⟨x + x', L.add_mem hx hx', by simp⟩
    | neg _ _ h1 =>
      obtain ⟨x, hx, rfl⟩ := h1
      exact ⟨-x, L.neg_mem hx, by simp⟩
  have hgen : ∀ v ∈ M.gen, v ∈ M.carrier := by
    intro v hv
    refine ⟨fun u => if u = v then 1 else 0, ?_⟩
    rw [Finset.sum_eq_single v]
    · simp
    · intro u _ hu
      simp [hu]
    · intro h; exact absurd hv h
  have hL : ∀ y, y ∈ AddSubgroup.closure {y | ∃ a : 𝓞 K, ∃ x ∈ e '' M.carrier, y = σ (a : K) • x} ↔
      ∃ c : N → 𝓞 K, y = e (∑ v ∈ M.gen, σ (c v : K) • v) := by
    intro y
    constructor
    · intro hy
      induction hy using AddSubgroup.closure_induction with
      | mem y hy =>
        obtain ⟨a, _, ⟨_, ⟨c, rfl⟩, rfl⟩, rfl⟩ := hy
        choose b hb using hφ
        refine ⟨fun v => a * b (c v), ?_⟩
        rw [← map_smul, Finset.smul_sum]
        simp [hb, mul_smul]
      | zero => exact ⟨0, by simp⟩
      | add _ _ _ _ h1 h2 =>
        obtain ⟨c, rfl⟩ := h1
        obtain ⟨c', rfl⟩ := h2
        refine ⟨c + c', ?_⟩
        rw [← map_add, ← Finset.sum_add_distrib]
        simp [add_smul]
      | neg _ _ h1 =>
        obtain ⟨c, rfl⟩ := h1
        refine ⟨-c, ?_⟩
        rw [← map_neg, ← Finset.sum_neg_distrib]
        simp
    · rintro ⟨c, rfl⟩
      rw [map_sum]
      refine AddSubgroup.sum_mem _ fun v hv => AddSubgroup.subset_closure ⟨c v, e v, ⟨v, hgen v hv, rfl⟩, map_smul _ _ _⟩
  refine ⟨fun v hv => ?_, fun x => ⟨fun hx => ?_, ?_⟩⟩
  · have h1 : e v ∈ AddSubgroup.closure {y | ∃ a : 𝓞 K, ∃ x ∈ e '' M.carrier, y = σ (a : K) • x} :=
      AddSubgroup.subset_closure ⟨1, e v, ⟨v, hgen v hv, rfl⟩, by simp⟩
    rw [h, hR] at h1
    obtain ⟨x, -, hx⟩ := h1
    exact ⟨x, he hx⟩
  · have h1 := (hR _).2 ⟨x, hx, rfl⟩
    rw [← h, hL] at h1
    obtain ⟨c, hc⟩ := h1
    exact ⟨c, he hc⟩
  · rintro ⟨c, hc⟩
    have h1 := (hL (e (j x))).2 ⟨c, congrArg e hc⟩
    rw [h, hR] at h1
    obtain ⟨x', hx', hxx⟩ := h1
    rwa [← hj (he hxx)]

/- English proof (translation)
Establish `hge : (LinearMap.ker th)ᗮ ≤ Submodule.span ℂ (Set.range fun k => J (E *ᵥ Pi.single k 1))`. Introduce `y hy`. Establish `h1` using `hsur y`. Rewrite `h1` using `[show (fun k => th (J (E *ᵥ Pi.single k 1))) = th ∘ fun k => J (E *ᵥ Pi.single k 1) from rfl, Set.range_comp, ← Submodule.map_span]`. Take `⟨z, hz, hzy⟩` from `h1`.

Establish `h2 : y - z ∈ LinearMap.ker th` using `by rw [LinearMap.mem_ker, map_sub, hzy, sub_self]`. Establish `h3 : y - z ∈ (LinearMap.ker th)ᗮ` using `sub_mem hy (hle hz)`. Establish `h4 : y - z = 0` using `inner_self_eq_zero.1 (h3 _ h2)`. Rewrite using `[sub_eq_zero.1 h4]`. Conclude with `hz`.

Rewrite using `[← sub_eq_zero, ← map_sub, ← LinearMap.mem_ker, ← Submodule.orthogonal_orthogonal (LinearMap.ker th)]`. Introduce `u hu`. Establish `h5 : Submodule.span ℂ (Set.range fun k => J (E *ᵥ Pi.single k 1)) ≤ (Submodule.span ℂ {J x - J (E *ᵥ (Pr *ᵥ x))})ᗮ`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨z, rfl⟩`.

Rewrite using `[SetLike.mem_coe, Submodule.mem_orthogonal_singleton_iff_inner_left, inner_sub_right, hin, hin, LiftForms.hform_orth hp, sub_self]`. Conclude with `Submodule.mem_orthogonal_singleton_iff_inner_left.1 (h5 (hge hu))`.
-/
theorem map_eq_map_proj [StarRing K] {M : Type} [NormedAddCommGroup M] [InnerProductSpace ℂ M] [FiniteDimensional ℂ M]
    (th : M →ₗ[ℂ] N) {n d : ℕ} (J : (Fin n → K) →ₛₗ[σ] M) {Hm : Matrix (Fin n) (Fin n) K} {E : Matrix (Fin n) (Fin d) K}
    {Pr : Matrix (Fin d) (Fin n) K} (hp : IsOrthProj Hm E Pr) (hin : ∀ x y, inner ℂ (J x) (J y) = σ (hform Hm x y))
    (hle : Submodule.span ℂ (Set.range fun k => J (E *ᵥ Pi.single k 1)) ≤ (LinearMap.ker th)ᗮ)
    (hsur : ∀ y, th y ∈ Submodule.span ℂ (Set.range fun k => th (J (E *ᵥ Pi.single k 1)))) (x : Fin n → K) :
    th (J x) = th (J (E *ᵥ (Pr *ᵥ x))) := by
  have hge : (LinearMap.ker th)ᗮ ≤ Submodule.span ℂ (Set.range fun k => J (E *ᵥ Pi.single k 1)) := by
    intro y hy
    have h1 := hsur y
    rw [show (fun k => th (J (E *ᵥ Pi.single k 1))) = th ∘ fun k => J (E *ᵥ Pi.single k 1) from rfl, Set.range_comp,
      ← Submodule.map_span] at h1
    obtain ⟨z, hz, hzy⟩ := h1
    have h2 : y - z ∈ LinearMap.ker th := by rw [LinearMap.mem_ker, map_sub, hzy, sub_self]
    have h3 : y - z ∈ (LinearMap.ker th)ᗮ := sub_mem hy (hle hz)
    have h4 : y - z = 0 := inner_self_eq_zero.1 (h3 _ h2)
    rw [sub_eq_zero.1 h4]
    exact hz
  rw [← sub_eq_zero, ← map_sub, ← LinearMap.mem_ker, ← Submodule.orthogonal_orthogonal (LinearMap.ker th)]
  intro u hu
  have h5 : Submodule.span ℂ (Set.range fun k => J (E *ᵥ Pi.single k 1)) ≤
      (Submodule.span ℂ {J x - J (E *ᵥ (Pr *ᵥ x))})ᗮ := by
    rw [Submodule.span_le]
    rintro _ ⟨z, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_orthogonal_singleton_iff_inner_left, inner_sub_right, hin, hin,
      LiftForms.hform_orth hp, sub_self]
  exact Submodule.mem_orthogonal_singleton_iff_inner_left.1 (h5 (hge hu))

omit [NumberField K] in
/- English proof (translation)
The claim follows from `(semi_expand w y).symm`.
-/
theorem lin_cpt {d : ℕ} (w : (Fin d → K) →ₛₗ[σ] H) (y : Fin d → K) :
    lin (fun k => w (Pi.single k 1)) (cpt σ y) = w y := (semi_expand w y).symm

end Core

section Lift

variable {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} {A : DefAmb Bs} (X : CxData A)
  {fc : DefSub A → DefFace Bs} (cr : Crd A fc) (b : Bool)

/- English proof (translation)
The claim follows from `(X.key_lift cr b h5 hr j t z).trans (lin_cpt (((X.θ' j t).comp (X.jL j t)).comp (cr.toL X.zs b j t)) z)`.
-/
theorem liftMatrix_computes_lift_rational (h5 : X.H5 cr b) (hr : X.RATth cr b) (j : Bs.J) (t : Bs.Tup) (z : Fin ((lv (fc X.zs) b).dZ j t) → K) :
    X.w0C b j (cpt Bs.v0.embedding (X.liftMat cr b j t *ᵥ z)) = X.θ' j t (X.jL j t (cr.toL X.zs b j t z)) :=
  (X.key_lift cr b h5 hr j t z).trans (lin_cpt (((X.θ' j t).comp (X.jL j t)).comp (cr.toL X.zs b j t)) z)

end Lift

section Main

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

/- English proof (translation)
Use `choose jW hj hjli hjsp using fun i => exists_form (e i) (he i) (w i) (hli i) (hsp i)`. Establish `hth' : ∀ i t z, jW i (S0.θ i t *ᵥ z) = D.what₂.thetaP (tup t) ((i : ℕ) + 1) (D.what₂.jMt (tup t) ((i : ℕ) + 1) (eMt i t (lZ0 D A P ψ Zs i t *ᵥ z)))` using `fun i t z => he i ((hj i _).trans (hth i t z))`. Use `⟨jW, ⟨hjli, hjsp, fun i => ?_, fun i t x => ?_⟩, hj⟩` and prove the remaining obligations. Use `oLatTie_of_closure (fun a => ⟨⟨D.what₂.OtoLL a, D.O_int a⟩, rfl⟩) _ (e i) (he i) (jW i) (semi_injective _ (hjli i)) _ (S i) (fun y => ?_) (hlat i)` and prove the remaining obligations. Simplify using `only [hj]`.

Conclude with `hS i y`. Establish `hB : BlockHyp (A.fam.L i t) (A.fam.lvlA P ψ) A.v0 s` using `⟨hOk.conj, hOk.irr, hOk.lifts i t⟩`. Establish `hp : IsOrthProj (lH D A P ψ i t) (lZ0 D A P ψ Zs i t) (lPrj D A P ψ Zs i t)` using `BlockDat.lf_l_proj hB`. Rewrite using `[hth']`. Use `map_eq_map_proj (D.what₂.thetaP (tup t) ((i : ℕ) + 1)) ((D.what₂.jMt (tup t) ((i : ℕ) + 1)).comp (eMt i t).toLinearMap) hp (hM.forms i t).inner ?_ (fun y => ?_) x` and prove the remaining obligations.

Conclude with `(hM.Z0 i t).ge.trans inf_le_left`. Establish `hle : Submodule.span ℂ (Set.range fun k => jW i (Pi.single k 1)) ≤ Submodule.span ℂ (Set.range fun k => D.what₂.thetaP (tup t) ((i : ℕ) + 1) (((D.what₂.jMt (tup t) ((i : ℕ) + 1)).comp (eMt i t).toLinearMap) (lZ0 D A P ψ Zs i t *ᵥ Pi.single k 1)))`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨k, rfl⟩`. Take `⟨z, hz⟩` from `hsur i t (Pi.single k 1)`.

Establish `h1` using `(LiftForms.span_range_mulVec ((D.what₂.thetaP (tup t) ((i : ℕ) + 1)).comp ((D.what₂.jMt (tup t) ((i : ℕ) + 1)).comp (eMt i t).toLinearMap)) (lZ0 D A P ψ Zs i t)).le`. Use `h1 (Submodule.subset_span ⟨_, ⟨z, rfl⟩, ?_⟩)` and prove the remaining obligations. Conclude with `(hth' i t z).symm.trans (congrArg (jW i) hz)`. Conclude with `hle (hjsp i ▸ Submodule.mem_top)`.
-/
theorem thTie_of_clauses {s : ℕ} (hOk : A.fam.Ok s) (P : Subgroup G) (ψ : P →* D.what₂.LLˣ) (Zs : DefSub A.fam.amb)
    (S0 : IndefData (A.side P ψ Zs)) (tup : T → D.what₂.Tup)
    (eMt : ∀ (i : Fin D.R.m) (t : T), (Fin (lDim D A P ψ i t) → D.what₂.LL) ≃ₗ[D.what₂.LL] D.what₂.MtL (tup t) ((i : ℕ) + 1))
    (hM : MtTie D A P ψ Zs tup eMt) {H : Fin D.R.m → Type} [∀ i, AddCommGroup (H i)] [∀ i, Module ℂ (H i)]
    (e : ∀ i : Fin D.R.m, D.what₂.Mj ((i : ℕ) + 1) →ₗ[ℂ] H i) (he : ∀ i, Function.Injective (e i))
    (w : ∀ i : Fin D.R.m, (Fin (S0.dW i) → D.what₂.LL) →ₛₗ[D.what₂.embLL] H i)
    (hli : ∀ i, LinearIndependent ℂ fun k => w i (Pi.single k 1))
    (hsp : ∀ i, Submodule.span ℂ (Set.range fun k => w i (Pi.single k 1)) = LinearMap.range (e i))
    (S : ∀ i, Set (H i)) (hS : ∀ i y, y ∈ S i ↔ ∃ x ∈ S0.M i, w i x = y)
    (hlat : ∀ i, intSpan D (e i '' (D.what₂.MjLat ((i : ℕ) + 1)).carrier) = intSpan D (S i))
    (hth : ∀ i t z, w i (S0.θ i t *ᵥ z) = e i (D.what₂.thetaP (tup t) ((i : ℕ) + 1)
      (D.what₂.jMt (tup t) ((i : ℕ) + 1) (eMt i t (lZ0 D A P ψ Zs i t *ᵥ z)))))
    (hsur : ∀ i t, Function.Surjective (S0.θ i t).mulVec) :
    ∃ jW, ThTie D A S0 tup eMt jW ∧ ∀ i y, e i (jW i y) = w i y := by
  choose jW hj hjli hjsp using fun i => exists_form (e i) (he i) (w i) (hli i) (hsp i)
  have hth' : ∀ i t z, jW i (S0.θ i t *ᵥ z) = D.what₂.thetaP (tup t) ((i : ℕ) + 1)
      (D.what₂.jMt (tup t) ((i : ℕ) + 1) (eMt i t (lZ0 D A P ψ Zs i t *ᵥ z))) :=
    fun i t z => he i ((hj i _).trans (hth i t z))
  refine ⟨jW, ⟨hjli, hjsp, fun i => ?_, fun i t x => ?_⟩, hj⟩
  · refine oLatTie_of_closure (fun a => ⟨⟨D.what₂.OtoLL a, D.O_int a⟩, rfl⟩) _ (e i) (he i) (jW i)
      (semi_injective _ (hjli i)) _ (S i) (fun y => ?_) (hlat i)
    simp only [hj]
    exact hS i y
  · have hB : BlockHyp (A.fam.L i t) (A.fam.lvlA P ψ) A.v0 s := ⟨hOk.conj, hOk.irr, hOk.lifts i t⟩
    have hp : IsOrthProj (lH D A P ψ i t) (lZ0 D A P ψ Zs i t) (lPrj D A P ψ Zs i t) := BlockDat.lf_l_proj hB
    rw [hth']
    refine map_eq_map_proj (D.what₂.thetaP (tup t) ((i : ℕ) + 1))
      ((D.what₂.jMt (tup t) ((i : ℕ) + 1)).comp (eMt i t).toLinearMap) hp (hM.forms i t).inner ?_ (fun y => ?_) x
    · exact (hM.Z0 i t).ge.trans inf_le_left
    · have hle : Submodule.span ℂ (Set.range fun k => jW i (Pi.single k 1)) ≤ Submodule.span ℂ (Set.range fun k =>
          D.what₂.thetaP (tup t) ((i : ℕ) + 1)
            (((D.what₂.jMt (tup t) ((i : ℕ) + 1)).comp (eMt i t).toLinearMap) (lZ0 D A P ψ Zs i t *ᵥ Pi.single k 1))) := by
        rw [Submodule.span_le]
        rintro _ ⟨k, rfl⟩
        obtain ⟨z, hz⟩ := hsur i t (Pi.single k 1)
        have h1 := (LiftForms.span_range_mulVec ((D.what₂.thetaP (tup t) ((i : ℕ) + 1)).comp
          ((D.what₂.jMt (tup t) ((i : ℕ) + 1)).comp (eMt i t).toLinearMap)) (lZ0 D A P ψ Zs i t)).le
        refine h1 (Submodule.subset_span ⟨_, ⟨z, rfl⟩, ?_⟩)
        exact (hth' i t z).symm.trans (congrArg (jW i) hz)
      exact hle (hjsp i ▸ Submodule.mem_top)

variable (R : RealDat D A Ks) (F : Face D A)

def goodForm (b : Bool) (i : Fin D.R.m) :
    (Fin (Module.finrank D.what₂.LL (R.WL F b i)) → D.what₂.LL) →ₛₗ[D.what₂.embLL] (R.HW i (sg0 D A)).H where
  toFun y := (R.FW i).j (sg0 D A) (∑ k, y k • R.bL F b i k)
  map_add' x y := by simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib, map_add]
  map_smul' a y := by
    have h : sg0 D A a = D.what₂.embLL a := by rw [sg0, sgAt_mk _ R.hv0]
    simp only [Pi.smul_apply, smul_eq_mul, mul_smul, ← Finset.smul_sum, map_smulₛₗ, h]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem goodForm_apply (b : Bool) (i : Fin D.R.m) (y : Fin (Module.finrank D.what₂.LL (R.WL F b i)) → D.what₂.LL) :
    goodForm R F b i y = (R.FW i).j (sg0 D A) (∑ k, y k • R.bL F b i k) := rfl

/- English proof (translation)
Rewrite using `[goodForm_apply]`. Use `congr 1`. Simplify using `[Pi.single_apply]`.
-/
theorem goodForm_single (b : Bool) (i : Fin D.R.m) (k : Fin (Module.finrank D.what₂.LL (R.WL F b i))) :
    goodForm R F b i (Pi.single k 1) = (R.FW i).j (sg0 D A) (R.bL F b i k) := by
  rw [goodForm_apply]
  congr 1
  simp [Pi.single_apply]

/- English proof (translation)
Simplify using `only [goodForm_single]`. Conclude with `(hU i _).1 _ _ ((Module.finBasis D.what₂.LL (R.WL F b i)).linearIndependent.map' (R.WL F b i).subtype (Submodule.ker_subtype _))`.
-/
theorem goodForm_li (hU : R.LUnif) (b : Bool) (i : Fin D.R.m) :
    LinearIndependent ℂ fun k => goodForm R F b i (Pi.single k 1) := by
  simp only [goodForm_single]
  exact (hU i _).1 _ _
    ((Module.finBasis D.what₂.LL (R.WL F b i)).linearIndependent.map' (R.WL F b i).subtype (Submodule.ker_subtype _))

/- English proof (translation)
Use `Real.sqrt_pos.2 (RealDat.nP_pos (F := F) b)` as an intermediate fact. Conclude with `this.ne'` after adjusting the coercions.
-/
theorem sqrt_ne (b : Bool) : ((Real.sqrt (RealDat.nP F b) : ℝ) : ℂ) ≠ 0 := by
  have := Real.sqrt_pos.2 (RealDat.nP_pos (F := F) b)
  exact_mod_cast this.ne'

/- English proof (translation)
Rewrite using `[goodForm_single, RealDat.bC, smul_smul, Complex.ofReal_inv, mul_inv_cancel₀ (sqrt_ne F b), one_smul]`.
-/
theorem smul_bC (b : Bool) (i : Fin D.R.m) (k : Fin (Module.finrank D.what₂.LL (R.WL F b i))) :
    ((Real.sqrt (RealDat.nP F b) : ℝ) : ℂ) • R.bC F b i (sg0 D A) k = goodForm R F b i (Pi.single k 1) := by
  rw [goodForm_single, RealDat.bC, smul_smul, Complex.ofReal_inv, mul_inv_cancel₀ (sqrt_ne F b), one_smul]

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨k, rfl⟩`. Rewrite using `[SetLike.mem_coe]`. Use `beta_reduce`.

Rewrite using `[← smul_bC]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)`. Rewrite using `[RealDat.WS, Submodule.span_le]`. Introduce and unpack `_ ⟨k, rfl⟩`. Rewrite using `[SetLike.mem_coe, ← Submodule.smul_mem_iff _ (sqrt_ne F b), smul_bC]`.

Conclude with `Submodule.subset_span ⟨k, rfl⟩`.
-/
theorem goodForm_span (b : Bool) (i : Fin D.R.m) :
    Submodule.span ℂ (Set.range fun k => goodForm R F b i (Pi.single k 1)) = R.WS F b i (sg0 D A) := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    rw [SetLike.mem_coe]
    beta_reduce
    rw [← smul_bC]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  · rw [RealDat.WS, Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    rw [SetLike.mem_coe, ← Submodule.smul_mem_iff _ (sqrt_ne F b), smul_bC]
    exact Submodule.subset_span ⟨k, rfl⟩

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨f, hf, rfl⟩`. Establish `hW : f ∈ R.WL F b i` using `(R.FW i).Mj_sub_Wgood _ _ _ hf`. Establish `hs : ∑ k, (Module.finBasis D.what₂.LL (R.WL F b i)).repr ⟨f, hW⟩ k • R.bL F b i k = f`. Establish `h` using `congrArg (R.WL F b i).subtype ((Module.finBasis D.what₂.LL (R.WL F b i)).sum_repr ⟨f, hW⟩)`.

Rewrite `h` using `[map_sum]`. Conclude with `h`. Use `⟨fun k => (Module.finBasis D.what₂.LL (R.WL F b i)).repr ⟨f, hW⟩ k, ((R.FW i).mem_Mcoord _ _ _ _ _).2 ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hs]`. Conclude with `hf`.

Conclude with `congrArg ((R.FW i).j (sg0 D A)) hs`. Introduce and unpack `⟨x, hx, rfl⟩`. Conclude with `⟨_, ((R.FW i).mem_Mcoord _ _ _ _ _).1 hx, rfl⟩`.
-/
theorem mem_image_iff (b : Bool) (i : Fin D.R.m) (y : (R.HW i (sg0 D A)).H) :
    y ∈ (R.FW i).j (sg0 D A) '' ((R.FW i).Mj (F.lvl b).P (F.lvl b).ψ⁻¹ (fun g => (idemOf A.X).coeff g) : Set _) ↔
      ∃ x ∈ (R.toCx F).M b i, goodForm R F b i x = y := by
  constructor
  · rintro ⟨f, hf, rfl⟩
    have hW : f ∈ R.WL F b i := (R.FW i).Mj_sub_Wgood _ _ _ hf
    have hs : ∑ k, (Module.finBasis D.what₂.LL (R.WL F b i)).repr ⟨f, hW⟩ k • R.bL F b i k = f := by
      have h := congrArg (R.WL F b i).subtype ((Module.finBasis D.what₂.LL (R.WL F b i)).sum_repr ⟨f, hW⟩)
      rw [map_sum] at h
      exact h
    refine ⟨fun k => (Module.finBasis D.what₂.LL (R.WL F b i)).repr ⟨f, hW⟩ k, ((R.FW i).mem_Mcoord _ _ _ _ _).2 ?_, ?_⟩
    · rw [hs]; exact hf
    · exact congrArg ((R.FW i).j (sg0 D A)) hs
  · rintro ⟨x, hx, rfl⟩
    exact ⟨_, ((R.FW i).mem_Mcoord _ _ _ _ _).1 hx, rfl⟩

/- English proof (translation)
Establish `h1 : (R.toCx F).w0C b i = lin fun k => Tw.semi _ R.emb0 (goodForm R F b i) (Pi.single k 1)`. Rewrite using `[← lin_basis ((R.toCx F).w0C b i)]`. Use `congr 1`. Use function extensionality and compare the values at `k`. Conclude with `(congrArg ((R.toCx F).eW b i) (lin_single _ k)).trans (smul_bC R F b i k)`.

Rewrite using `[h1]`. Conclude with `lin_cpt (Tw.semi _ R.emb0 (goodForm R F b i)) y`.
-/
theorem liftWeight_complexPoint_eq_twist (b : Bool) (i : Fin D.R.m) (y : Fin (Module.finrank D.what₂.LL (R.WL F b i)) → D.what₂.LL) :
    (R.toCx F).w0C b i (cpt A.v0.embedding y) = Tw.mk (twAt D.what₂.embLL A.v0) (goodForm R F b i y) := by
  have h1 : (R.toCx F).w0C b i = lin fun k => Tw.semi _ R.emb0 (goodForm R F b i) (Pi.single k 1) := by
    rw [← lin_basis ((R.toCx F).w0C b i)]
    congr 1
    funext k
    exact (congrArg ((R.toCx F).eW b i) (lin_single _ k)).trans (smul_bC R F b i k)
  rw [h1]
  exact lin_cpt (Tw.semi _ R.emb0 (goodForm R F b i)) y

/- English proof (translation)
The claim follows from `LiftForms.lvlForm_lE (v0 := A.v0) (s := s) ⟨hOk.conj, hOk.irr, hOk.lifts i t⟩ z`.
-/
theorem levelFormCoordinateMap_levelZero {s : ℕ} (hOk : A.fam.Ok s) (Zs : DefSub A.fam.amb) (i : Fin D.R.m) (t : T)
    (z : Fin ((A.fam.L i t).dZ (A.fam.lvlA F.P0 F.ψ0) (Zs.Zl i t)) → D.what₂.LL) :
    LiftForms.lvlForm (A.fam.L i t).S (A.fam.L i t).r (A.fam.lvlA F.P0 F.ψ0).P (A.fam.lvlA F.P0 F.ψ0).ψ
      (lZ0 D A F.P0 F.ψ0 Zs i t *ᵥ z) = F.cr.toL Zs false i t z :=
  LiftForms.lvlForm_lE (v0 := A.v0) (s := s) ⟨hOk.conj, hOk.irr, hOk.lifts i t⟩ z

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Use `thTie_of_clauses hOk F.P0 F.ψ0 (R.toCx F).zs ((R.toCx F).data F.cr false) Y.tup eMt hM Y.eW Y.eW_injective (goodForm R F false) (goodForm_li R F hU false) (fun i => ?_) _ (mem_image_iff R F false) Y.eW_lat (fun i t z => ?_) (fun i t => ((R.toCx F).liftMat_bij F.cr false (RealDat. …` and prove the remaining obligations. Conclude with `(goodForm_span R F false i).trans ((hL false i _).trans (Y.eW_range i).symm)`. Establish `h1` using `(liftWeight_complexPoint_eq_twist R F false i _).symm.trans (liftMatrix_computes_lift_rational (R.toCx F) F.cr false (hT false) (hR false) i t z)`. Establish `h2` using `(Y.theta_tie i t _).trans (congrArg (R.thG i t) ((hco i t _).trans (congrArg (R.jV i t) (levelFormCoordinateMap_levelZero F hOk (R.toCx F).zs i t z))))`. Conclude with `h1.trans h2.symm`.
-/
theorem exists_thTie_of_coord {s : ℕ} (X0 : BaseLevelRowSide D) (hOk : A.fam.Ok s) (hU : R.LUnif) (hL : R.LLevelW F) (hT : R.LTheta F)
    (hR : R.LRatTh F) (Y : RowsTie R F X0)
    (eMt : ∀ (i : Fin D.R.m) (t : T),
      (Fin (lDim D A F.P0 F.ψ0 i t) → D.what₂.LL) ≃ₗ[D.what₂.LL] D.what₂.MtL (Y.tup t) ((i : ℕ) + 1))
    (hM : MtTie D A F.P0 F.ψ0 (R.toCx F).zs Y.tup eMt)
    (hco : ∀ (i : Fin D.R.m) (t : T) x, Y.eV i t (D.what₂.jMt (Y.tup t) ((i : ℕ) + 1) (eMt i t x)) =
      R.jV i t (LiftForms.lvlForm (A.fam.L i t).S (A.fam.L i t).r (A.fam.lvlA F.P0 F.ψ0).P (A.fam.lvlA F.P0 F.ψ0).ψ x)) :
    ∃ jW, ThTie D A (P0 := F.P0) (ψ0 := F.ψ0) (Zs := (R.toCx F).zs) ((R.toCx F).data F.cr false) Y.tup eMt jW ∧
      ∀ i y, Y.eW i (jW i y) = goodForm R F false i y := by
  refine thTie_of_clauses hOk F.P0 F.ψ0 (R.toCx F).zs ((R.toCx F).data F.cr false) Y.tup eMt hM Y.eW Y.eW_injective
    (goodForm R F false) (goodForm_li R F hU false) (fun i => ?_) _ (mem_image_iff R F false) Y.eW_lat (fun i t z => ?_)
    (fun i t => ((R.toCx F).liftMat_bij F.cr false (RealDat.kForm hU false) (RealDat.ewNorm false) (RealDat.nP_pos false)
      (hT false) (hR false) i t).2)
  · exact (goodForm_span R F false i).trans ((hL false i _).trans (Y.eW_range i).symm)
  · have h1 := (liftWeight_complexPoint_eq_twist R F false i _).symm.trans (liftMatrix_computes_lift_rational (R.toCx F) F.cr false (hT false) (hR false) i t z)
    have h2 := (Y.theta_tie i t _).trans (congrArg (R.thG i t) ((hco i t _).trans
      (congrArg (R.jV i t) (levelFormCoordinateMap_levelZero F hOk (R.toCx F).zs i t z))))
    exact h1.trans h2.symm

/- English proof (translation)
Establish `h` using `LiftForms.exists_mtTie_coord R F X0 hC hOk hZ hS Y`. Use `h.elim fun e he => ?_` and prove the remaining obligations. Establish `h'` using `exists_thTie_of_coord R F X0 hOk hU hL hT hR Y e he.1 fun i t => (he.2 i t).1`. Conclude with `h'.elim fun jW hj => ⟨e, jW, he.1, hj.1, fun i t => (he.2 i t).1, hj.2⟩`.
-/
theorem exists_mtTie_thTie {s : ℕ} (X0 : BaseLevelRowSide D) (hC : R.Char F) (hOk : A.fam.Ok s) (hZ : R.LRatZ F) (hS : R.LStable F)
    (hU : R.LUnif) (hL : R.LLevelW F) (hT : R.LTheta F) (hR : R.LRatTh F) (Y : RowsTie R F X0) :
    ∃ eMt jW, MtTie D A F.P0 F.ψ0 (R.toCx F).zs Y.tup eMt ∧
      ThTie D A (P0 := F.P0) (ψ0 := F.ψ0) (Zs := (R.toCx F).zs) ((R.toCx F).data F.cr false) Y.tup eMt jW ∧
      (∀ (i : Fin D.R.m) (t : T) x, Y.eV i t (D.what₂.jMt (Y.tup t) ((i : ℕ) + 1) (eMt i t x)) =
        R.jV i t (LiftForms.lvlForm (A.fam.L i t).S (A.fam.L i t).r (A.fam.lvlA F.P0 F.ψ0).P (A.fam.lvlA F.P0 F.ψ0).ψ x)) ∧
      ∀ i y, Y.eW i (jW i y) = goodForm R F false i y := by
  have h := LiftForms.exists_mtTie_coord R F X0 hC hOk hZ hS Y
  refine h.elim fun e he => ?_
  have h' := exists_thTie_of_coord R F X0 hOk hU hL hT hR Y e he.1 fun i t => (he.2 i t).1
  exact h'.elim fun jW hj => ⟨e, jW, he.1, hj.1, fun i t => (he.2 i t).1, hj.2⟩

end Main

end GlobalTheory.Mem.LiftTheta

end
