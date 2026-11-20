import Formalism.SharpRestriction.GrowthBounds.DualFockLinear.RestCloudBOfThree
import Formalism.LocalToGlobal.GroupLattices.FockModels.Cartan
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ProductFirstParts

noncomputable section

namespace Formalism.MainNotions.TestSideCounting

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14 MvPolynomial
open Formalism.MainNotions.G.LatticeSystems (lb_D lb_D_det kp_lamAt_antitone)

section Tensor

variable {R K : Type} [CommRing R] [Field K] [Algebra R K] {S : Type} [Fintype S] [DecidableEq S] {k n : ℕ}

/- English proof (translation)
The claim follows from `_root_.UpperTheory.Reformulated.B.product_first_partition.tensor_onto A B M hM`.
-/
theorem tensor_onto (A B M : S → Submodule R (MvPolynomial (Fin k × Fin n) K))
    (hM : ∀ s, M s ≤ Submodule.span R {X | ∃ F ∈ A s, ∃ G ∈ B s, X = F * G}) :
    tensorLat R K M ≤ Submodule.span R {X | ∃ P ∈ tensorLat R K A, ∃ Q ∈ tensorLat R K B, X = P * Q} :=
  _root_.UpperTheory.Reformulated.B.product_first_partition.tensor_onto A B M hM

end Tensor

/- English proof (translation)
Introduce `p n' W Qq O Kf _ _ _ _ _ _ _ _ _ _ ι σ j w h m r d rest lam hlam hdr e he z hz`. Establish `hw` using `w_ne_zero h`. Use `h.frac_O` as an intermediate fact. Establish `hfd : IsDominant (flW (m` using `m) d) := flW_dom _`. Establish `hAr : Ar r lam = Ar r (flW (m` using `m) d) + Ar r rest := by rw [hlam]; exact Ar_add r _ _`.

Take `⟨gs, hgs, _, h2, _⟩` from `Formalism.L2.G.Model.edgeLat h m r e he`. Establish `hΛ : ∀ s : Fin n', ∃ g : Matrix (Fin (m + 1)) (Fin (m + 1)) Kf, IsUnit g.det ∧ LeAt p ι σ w s.val e = colSpan O g` using `fun s => ⟨_, by rw [Matrix.det_mul]; exact (hgs _).mul (lb_D_det _ _ _ hw), h2 s.val⟩`. Use `set cw : Kf := algebraMap O Kf w with hcw`. Use `set Sp := Submodule.span O {z : Vsp Kf lam | ∃ y ∈ Re p ι σ w r (flW d) e, ∃ β ∈ Re p ι σ w r rest e, (z : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) = (y : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) * (β : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + …`. Take `⟨z0, hz0, rfl⟩` from `mem_scale.1 hz`.

Establish `hz0' : ((z0 : Vsp Kf lam) : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) ∈ Hten O lam (fun s => LeAt p ι σ w s.val e)` using `hz0`. Establish `hten` using `tensor_onto (R := O) (fun s => H0 O m (lamAt (flW (m := m) d) s) (LeAt p ι σ w s.val e)) (fun s => H0 O m (lamAt rest s) (LeAt p ι σ w s.val e)) (fun s => H0 O m (lamAt lam s) (LeAt p ι σ w s.val e)) (fun s => by`. Rewrite using `[hlam, lamAt_add]`. Conclude with `le_of_eq (Formalism.L2.G.Model.cartanOnto_proved O Kf m _ _ _ (hΛ s) (kp_lamAt_antitone _ hfd s) (kp_lamAt_antitone _ hdr s))) hz0'`. Establish `key : ∀ x ∈ Submodule.span O {X | ∃ P ∈ Hten O (flW (m` using `m) d) (fun s => LeAt p ι σ w s.val e), ∃ Q ∈ Hten O rest (fun s => LeAt p ι σ w s.val e), X = P * Q}, ∃ hx : x ∈ Vsp Kf lam, cw ^ (-Ar r lam) • (⟨x, hx⟩ : Vsp Kf lam) ∈ Sp := by`.

Introduce `x hx`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨P, hP, Q, hQ, rfl⟩` from `hx`. Establish `hPV` using `Hten_le_V hfd _ hΛ P hP`.

Establish `hQV` using `Hten_le_V hdr _ hΛ Q hQ`. Use `⟨V_mul Kf hlam hfd hdr hPV hQV, Submodule.subset_span ⟨cw ^ (-Ar r (flW (m := m) d)) • ⟨P, hPV⟩, mem_scale.2 ⟨⟨P, hPV⟩, hP, rfl⟩, cw ^ (-Ar r rest) • ⟨Q, hQV⟩, mem_scale.2 ⟨⟨Q, hQV⟩, hQ, rfl⟩, ?_⟩⟩` and prove the remaining obligations. Simplify using `only [Submodule.coe_smul]`. Rewrite using `[smul_mul_smul_comm, ← zpow_add₀ hw, hAr]`. Use `congr 2`.

Expand and normalize the polynomial expressions, which then agree. Consider the case `zero => exact ⟨Submodule.zero_mem _, by`. Establish `: (⟨0, Submodule.zero_mem _⟩ : Vsp Kf lam) = 0` using `rfl`. Rewrite using `[this, smul_zero]`. Conclude with `Submodule.zero_mem _⟩`.

Consider the case `add a b _ _ ha hb`. Take `⟨ha1, ha2⟩` from `ha`. Take `⟨hb1, hb2⟩` from `hb`. Use `⟨Submodule.add_mem _ ha1 hb1, ?_⟩` and prove the remaining obligations. Establish `: (⟨a + b, Submodule.add_mem _ ha1 hb1⟩ : Vsp Kf lam) = ⟨a, ha1⟩ + ⟨b, hb1⟩` using `rfl`.

Rewrite using `[this, smul_add]`. Conclude with `Submodule.add_mem _ ha2 hb2`. Consider the case `smul t a _ ha`. Take `⟨ha1, ha2⟩` from `ha`. Establish `hta : t • a ∈ Vsp Kf lam`.

Rewrite using `[← algebraMap_smul Kf t a]`. Conclude with `Submodule.smul_mem _ _ ha1`. Use `⟨hta, ?_⟩` and prove the remaining obligations. Establish `: (⟨t • a, hta⟩ : Vsp Kf lam) = t • ⟨a, ha1⟩` using `rfl`. Rewrite using `[this, smul_comm]`.

Conclude with `Submodule.smul_mem _ _ ha2`. Take `⟨hx, hmem⟩` from `key _ hten`. Conclude with `hmem`.
-/
theorem ontoAll : OntoAll := by
  intro p n' W Qq O Kf _ _ _ _ _ _ _ _ _ _ ι σ j w h m r d rest lam hlam hdr e he z hz
  have hw := w_ne_zero h
  have := h.frac_O
  have hfd : IsDominant (flW (m := m) d) := flW_dom _
  have hAr : Ar r lam = Ar r (flW (m := m) d) + Ar r rest := by rw [hlam]; exact Ar_add r _ _
  obtain ⟨gs, hgs, _, h2, _⟩ := Formalism.L2.G.Model.edgeLat h m r e he
  have hΛ : ∀ s : Fin n', ∃ g : Matrix (Fin (m + 1)) (Fin (m + 1)) Kf, IsUnit g.det ∧
      LeAt p ι σ w s.val e = colSpan O g := fun s =>
    ⟨_, by rw [Matrix.det_mul]; exact (hgs _).mul (lb_D_det _ _ _ hw), h2 s.val⟩
  set cw : Kf := algebraMap O Kf w with hcw
  set Sp := Submodule.span O {z : Vsp Kf lam | ∃ y ∈ Re p ι σ w r (flW d) e,
    ∃ β ∈ Re p ι σ w r rest e, (z : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) = (y : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) * (β : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf)} with hSp
  obtain ⟨z0, hz0, rfl⟩ := mem_scale.1 hz
  have hz0' : ((z0 : Vsp Kf lam) : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) ∈ Hten O lam (fun s => LeAt p ι σ w s.val e) := hz0
  have hten := tensor_onto (R := O) (fun s => H0 O m (lamAt (flW (m := m) d) s) (LeAt p ι σ w s.val e))
    (fun s => H0 O m (lamAt rest s) (LeAt p ι σ w s.val e)) (fun s => H0 O m (lamAt lam s) (LeAt p ι σ w s.val e))
    (fun s => by
      rw [hlam, lamAt_add]
      exact le_of_eq (Formalism.L2.G.Model.cartanOnto_proved O Kf m _ _ _ (hΛ s) (kp_lamAt_antitone _ hfd s)
        (kp_lamAt_antitone _ hdr s))) hz0'
  have key : ∀ x ∈ Submodule.span O {X | ∃ P ∈ Hten O (flW (m := m) d) (fun s => LeAt p ι σ w s.val e),
      ∃ Q ∈ Hten O rest (fun s => LeAt p ι σ w s.val e), X = P * Q},
      ∃ hx : x ∈ Vsp Kf lam, cw ^ (-Ar r lam) • (⟨x, hx⟩ : Vsp Kf lam) ∈ Sp := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨P, hP, Q, hQ, rfl⟩ := hx
      have hPV := Hten_le_V hfd _ hΛ P hP
      have hQV := Hten_le_V hdr _ hΛ Q hQ
      refine ⟨V_mul Kf hlam hfd hdr hPV hQV, Submodule.subset_span
        ⟨cw ^ (-Ar r (flW (m := m) d)) • ⟨P, hPV⟩, mem_scale.2 ⟨⟨P, hPV⟩, hP, rfl⟩,
          cw ^ (-Ar r rest) • ⟨Q, hQV⟩, mem_scale.2 ⟨⟨Q, hQV⟩, hQ, rfl⟩, ?_⟩⟩
      simp only [Submodule.coe_smul]
      rw [smul_mul_smul_comm, ← zpow_add₀ hw, hAr]
      congr 2
      ring
    | zero => exact ⟨Submodule.zero_mem _, by
        have : (⟨0, Submodule.zero_mem _⟩ : Vsp Kf lam) = 0 := rfl
        rw [this, smul_zero]; exact Submodule.zero_mem _⟩
    | add a b _ _ ha hb =>
      obtain ⟨ha1, ha2⟩ := ha
      obtain ⟨hb1, hb2⟩ := hb
      refine ⟨Submodule.add_mem _ ha1 hb1, ?_⟩
      have : (⟨a + b, Submodule.add_mem _ ha1 hb1⟩ : Vsp Kf lam) = ⟨a, ha1⟩ + ⟨b, hb1⟩ := rfl
      rw [this, smul_add]
      exact Submodule.add_mem _ ha2 hb2
    | smul t a _ ha =>
      obtain ⟨ha1, ha2⟩ := ha
      have hta : t • a ∈ Vsp Kf lam := by
        rw [← algebraMap_smul Kf t a]
        exact Submodule.smul_mem _ _ ha1
      refine ⟨hta, ?_⟩
      have : (⟨t • a, hta⟩ : Vsp Kf lam) = t • ⟨a, ha1⟩ := rfl
      rw [this, smul_comm]
      exact Submodule.smul_mem _ _ ha2
  obtain ⟨hx, hmem⟩ := key _ hten
  exact hmem

/- English proof (translation)
The claim follows from `restCloudB_of_three D CLa Ck Crk Cdeg hop hsz ontoAll`.
-/
theorem restCloudB_of_two (D : Formalism.BasicNotions.D7) (CLa Ck Crk Cdeg : ℝ) (hop : RestTSOp D CLa Ck Crk Cdeg) (hsz : RestSize) :
    RestCloudB D CLa Ck Crk Cdeg :=
  restCloudB_of_three D CLa Ck Crk Cdeg hop hsz ontoAll

end Formalism.MainNotions.TestSideCounting
