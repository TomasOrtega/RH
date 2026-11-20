import Formalism.HermitianCurvature.HermitianCurvatureProofs.RootVectorActionCutoff
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ResGContDiffAt
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RadialRaisingTopOfParts

open Matrix

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBN.MC

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.Qx5 Formalism.FourierDecayAlt.P.Qx2

section claim

variable {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {D : Set (Mx k r)} (hD : IsOpen D)
  (v₀ : VS k r 0 D E) (g₀ : Mx k r) (y : ℂ)

/- English proof (translation)
Establish `hγ` using `hcell c hc`. Use `set h : Mx k r → E := ((x : Module.End ℂ (VS k r 0 D E)) v₀ : Mx k r → E) with hh`. Use `set H : (Fin r → ℂ) → E := fun c' => h (wCell k r (Fin.last r) c' * g₀) with hH`. Establish `e1 : (((Tm (EA hD) ((y + ((2 * r + k : ℕ) : ℂ) / 2) - ((l : ℕ) : ℂ)) (eI k r l) (eI k r l) * x : SA E hD) : Module.End ℂ (VS k r 0 D E)) v₀ : Mx k r → E) (wCell k r (Fin.last r) c * g₀) = ((y + ((2 * r + k : ℕ) : ℂ) / 2) - ((l : ℕ) : ℂ)) • H c + pOp l H c`. Simplify using `only [Tm, Subalgebra.coe_mul, Subalgebra.coe_add, Module.End.mul_apply, LinearMap.add_apply, EA_val, Submodule.coe_add, Pi.add_apply, ite_true, if_true, Subalgebra.coe_algebraMap, Module.algebraMap_end_apply, Submodule.coe_smul, Pi.smul_apply]`.

Rewrite using `[ev_E hD _ _ _ hγ, posL_cI, hTC E k r D h hD ((x : Module.End ℂ (VS k r 0 D E)) v₀).2.1 c hc g₀ hg₀ hγ.2 l]`. Rewrite using `[resG_last, e1]`. Simplify using `only [resG_last]`. Rewrite using `[hGP E r (fun a => Mdim k r a - 1) H c hc (hdiff x c hc) l]`. Establish `hw : (y + ((2 * r + k : ℕ) : ℂ) / 2) - ((l : ℕ) : ℂ) = y + ((Mdim k r l - 1 : ℕ) : ℂ) / 2`.

Establish `hl` using `l.isLt`. Establish `e : Mdim k r l - 1 = 2 * (r - l.val) + k` using `by simp [Mdim]`. Rewrite using `[e]`. Move the coercions through the operations in `[Nat.cast_sub hl.le]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[hw]`. Use `module`.
-/
theorem torus_step (hTC : TorusCell) (hGP : GaugeP) (hg₀ : g₀ ∈ Glev k r (Fin.last r))
    (hcell : ∀ c ∈ OmX r, wCell k r (Fin.last r) c * g₀ ∈ Glev k r 0 ∩ D)
    (hdiff : ∀ x : SA E hD, ∀ c ∈ OmX r,
      DifferentiableAt ℝ (fun c' => ((x : Module.End ℂ (VS k r 0 D E)) v₀ : Mx k r → E) (wCell k r (Fin.last r) c' * g₀)) c)
    (l : Fin r) (x : SA E hD) (c : Fin r → ℂ) (hc : c ∈ OmX r) :
    Q.resG k r (Fin.last r) (((Tm (EA hD) ((y + ((2 * r + k : ℕ) : ℂ) / 2) - ((l : ℕ) : ℂ)) (eI k r l) (eI k r l) * x :
        SA E hD) : Module.End ℂ (VS k r 0 D E)) v₀ : Mx k r → E) c g₀ =
      y • Q.resG k r (Fin.last r) (((x : Module.End ℂ (VS k r 0 D E)) v₀ : Mx k r → E)) c g₀ +
        pOp l (fun c' => Q.resG k r (Fin.last r) (((x : Module.End ℂ (VS k r 0 D E)) v₀ : Mx k r → E)) c' g₀) c := by
  have hγ := hcell c hc
  set h : Mx k r → E := ((x : Module.End ℂ (VS k r 0 D E)) v₀ : Mx k r → E) with hh
  set H : (Fin r → ℂ) → E := fun c' => h (wCell k r (Fin.last r) c' * g₀) with hH
  have e1 : (((Tm (EA hD) ((y + ((2 * r + k : ℕ) : ℂ) / 2) - ((l : ℕ) : ℂ)) (eI k r l) (eI k r l) * x : SA E hD) :
      Module.End ℂ (VS k r 0 D E)) v₀ : Mx k r → E) (wCell k r (Fin.last r) c * g₀) =
      ((y + ((2 * r + k : ℕ) : ℂ) / 2) - ((l : ℕ) : ℂ)) • H c + pOp l H c := by
    simp only [Tm, Subalgebra.coe_mul, Subalgebra.coe_add, Module.End.mul_apply, LinearMap.add_apply, EA_val,
      Submodule.coe_add, Pi.add_apply, ite_true, if_true, Subalgebra.coe_algebraMap, Module.algebraMap_end_apply,
      Submodule.coe_smul, Pi.smul_apply]
    rw [ev_E hD _ _ _ hγ, posL_cI, hTC E k r D h hD ((x : Module.End ℂ (VS k r 0 D E)) v₀).2.1 c hc g₀ hg₀ hγ.2 l]
  rw [resG_last, e1]
  simp only [resG_last]
  rw [hGP E r (fun a => Mdim k r a - 1) H c hc (hdiff x c hc) l]
  have hw : (y + ((2 * r + k : ℕ) : ℂ) / 2) - ((l : ℕ) : ℂ) = y + ((Mdim k r l - 1 : ℕ) : ℂ) / 2 := by
    have hl := l.isLt
    have e : Mdim k r l - 1 = 2 * (r - l.val) + k := by simp [Mdim]
    rw [e]
    push_cast [Nat.cast_sub hl.le]
    ring
  rw [hw]
  module

end claim

/- English proof (translation)
Unfold `qminor`. Rewrite using `[Fintype.sum_unique]`. Simplify using `[List.ofFn_succ]`.
-/
theorem qminor_one {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} (E : Fin n → Fin n → A) (a b : Fin 1 → Fin n) (u : ℂ) :
    qminor E a b u = Tm E u (a 0) (b 0) := by
  unfold qminor
  rw [Fintype.sum_unique]
  simp [List.ofFn_succ]

/- English proof (translation)
Unfold `qminor`. Rewrite using `[Fintype.sum_unique]`. Simplify using the standard rewrite rules.
-/
theorem qminor_zero {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} (E : Fin n → Fin n → A) (a b : Fin 0 → Fin n) (u : ℂ) :
    qminor E a b u = 1 := by
  unfold qminor
  rw [Fintype.sum_unique]
  simp

section vab

variable {r : ℕ} {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

/- English proof (translation)
Simplify using `only [Q.vAB, dif_pos hi]`. Conclude with `⟨funext fun c => rfl, trivial⟩`.
-/
theorem vAB_succ (y : ℂ) (i : ℕ) (hi : i < r) (G : (Fin r → ℂ) → V) :
    (Q.vAB r y (i + 1)).1 G = (fun c => y • (Q.vAB r y i).1 G c + pOp ⟨i, hi⟩ ((Q.vAB r y i).1 G) c -
      cOp ⟨i, hi⟩ ((Q.vAB r y i).2 G) c) ∧
    (Q.vAB r y (i + 1)).2 G = ciOp ⟨i, hi⟩ ((Q.vAB r y i).1 G) := by
  simp only [Q.vAB, dif_pos hi]
  exact ⟨funext fun c => rfl, trivial⟩

end vab

section claim2

variable {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {D : Set (Mx k r)} (hD : IsOpen D)
  (v₀ : VS k r 0 D E) (g₀ : Mx k r) (y : ℂ)

/- English proof (translation)
Introduce `g hg n hn`. Rewrite using `[cut_of_mem f ⟨Formalism.FourierDecayAlt.P.Qx3.glev_mul hn.2 hg.1, hN g hg n hn⟩, cut_of_mem f hg]`. Conclude with `hLf g hg n hn`.
-/
theorem leftEq_cut (z : Fin (2 * r + k + 1) → ℂ) (hN : ∀ g ∈ Glev k r 0 ∩ D, ∀ n ∈ Nlev k r 0, n * g ∈ D)
    {f : Mx k r → E} (hLf : LeftEq k r z 0 D f) : LeftEq k r z 0 D (cut k r 0 D f) := by
  intro g hg n hn
  rw [cut_of_mem f ⟨Formalism.FourierDecayAlt.P.Qx3.glev_mul hn.2 hg.1, hN g hg n hn⟩, cut_of_mem f hg]
  exact hLf g hg n hn

/- English proof (translation)
Establish `hLv : LeftEq k r z 0 D (v₀ : Mx k r → E)` using `by rw [hv]; exact leftEq_cut z hN hLf`. Introduce `m`. Proceed by induction on `m using Nat.strong_induction_on with`. Consider the case `_ m ih`. Introduce `hm P hP c hc`.

Break down `m with _ | _ | m` into its components or cases. Rewrite using `[qminor_zero, one_mul]`. Both sides reduce to the same expression. Rewrite using `[qminor_one]`. Establish `hx0 : C3.xR k r 1 hm 0 = eI k r ⟨0, by omega⟩` using `by ext; simp [C3.xR, eI]`.

Establish `hts` using `torus_step hD v₀ g₀ y hTC hGP hg₀ hcell hdiff ⟨0, by omega⟩ P c hc`. Simplify using `only [Fin.val_mk, Nat.cast_zero, sub_zero] at hts`. Rewrite using `[hx0, hts, (vAB_succ y 0 (show 0 < r by omega) _).1]`. Simplify using `[Q.vAB, cOp]`. Establish `hm2 : m + 2 ≤ r` using `hm`.

Establish `hP1 : P ∈ Tor hD (m + 1)` using `Tor_mono hD (by omega) hP`. Establish `hP0 : P ∈ Tor hD m` using `Tor_mono hD (by omega) hP`. Use `set u : ℂ := y + ((2 * r + k : ℕ) : ℂ) / 2 with hu`. Use `set LaP : SA E hD →ₗ[ℂ] E := (La hD v₀ (wCell k r (Fin.last r) c * g₀)).comp (LinearMap.mulRight ℂ P) with hLaP`. Establish `hLaP_apply : ∀ x, LaP x = La hD v₀ (wCell k r (Fin.last r) c * g₀) (x * P)` using `fun x => rfl`.

Establish `hnot : ∀ (a : ℕ) (ha : a < m + 2), ∀ l' : Fin r, m + 2 ≤ l'.val → eI k r ⟨a, by omega⟩ ≠ eI k r l'`. Introduce `a ha l' hl' e`. Use `congrArg Fin.val e` as an intermediate fact. Simplify using `[eI] at this`. Use linear arithmetic over natural numbers and integers.

Establish `hR0 : ∀ (x : SA E hD) (l : ℕ) (hl : l < m), LaP (x * EA hD (eI k r ⟨l, by omega⟩) (eI k r ⟨m + 1, by omega⟩)) = 0`. Introduce `x l hl`. Rewrite using `[hLaP_apply, mul_assoc, (comm_Tor hD (m + 2) _ _ (hnot l (by omega)) (hnot (m + 1) (by omega)) P hP).eq, ← mul_assoc, La_apply, Subalgebra.coe_mul, Module.End.mul_apply]`. Use `conv_lhs => rw [hv]`. Rewrite using `[root_vector_action_cutoff hD z' hz' hRR hf hRf ⟨l, by omega⟩ ⟨m + 1, by omega⟩ (by simp; omega), if_neg (by simp; omega), zero_smul, map_zero]`.

Both sides reduce to the same expression. Establish `hR1 : ∀ x : SA E hD, LaP (x * EA hD (eI k r ⟨m, by omega⟩) (eI k r ⟨m + 1, by omega⟩)) = LaP x`. Introduce `x`. Rewrite using `[hLaP_apply, hLaP_apply, mul_assoc, (comm_Tor hD (m + 2) _ _ (hnot m (by omega)) (hnot (m + 1) (by omega)) P hP).eq, ← mul_assoc, La_apply, La_apply, Subalgebra.coe_mul, Module.End.mul_apply]`. Use `conv_lhs => rw [hv]`.

Rewrite using `[root_vector_action_cutoff hD z' hz' hRR hf hRf ⟨m, by omega⟩ ⟨m + 1, by omega⟩ (by simp), if_pos (by simp), one_smul, ← hv]`. Establish `hL : ∀ (x : SA E hD) (q : ℕ) (hq : q ≤ m), LaP (EA hD (eI k r ⟨m + 1, by omega⟩) (eI k r ⟨q, by omega⟩) * x) = (if q = m then c ⟨m + 1, by omega⟩ / c ⟨m, by omega⟩ else 0) • LaP x`. Introduce `x q hq`. Rewrite using `[hLaP_apply, hLaP_apply, mul_assoc, La_apply, La_apply, Subalgebra.coe_mul, Module.End.mul_apply, EA_val, ev_E hD _ _ _ (hcell c hc), posL_cI, posL_cI]`. Establish `hsm` using `(((x * P : SA E hD) : Module.End ℂ (VS k r 0 D E)) v₀).2.1`.

Establish `hle` using `leftEq_SA hD z hN (x * P) v₀ hLv`. Rewrite using `[hLR E k r z D _ hz hD hN hsm hle c hc g₀ hg₀ (hcell c hc).2 ⟨m + 1, by omega⟩ ⟨q, by omega⟩ (by simp; omega)]`. Use `congr 1`. Distinguish the cases in `hqm : q = m`. Substitute `hqm` using the available equality.

Simplify using the standard rewrite rules. Rewrite using `[if_neg (by simp; omega), if_neg hqm]`. Establish `hX` using `Formalism.FourierDecayAlt.P.PBN.chainX1' k r c (EA (E := E) hD) LaP (EA_gl (E := E) hD) m hm2 u hR0 hR1 hL`. Use `set T := Tm (EA (E := E) hD) (u - ((m + 1 : ℕ) : ℂ)) (eI k r ⟨m + 1, by omega⟩) (eI k r ⟨m + 1, by omega⟩) with hT`. Establish `hTmem : T ∈ Tor hD (m + 1)`.

Rewrite using `[hT]`. Unfold `Tm`. Rewrite using `[if_pos rfl]`. Conclude with `Subalgebra.add_mem _ (Subalgebra.algebraMap_mem _ _) (EA_mem_Tor hD ⟨m + 1, by omega⟩ le_rfl)`. Establish `hTP : T * P ∈ Tor hD (m + 1)` using `Subalgebra.mul_mem _ hTmem hP1`.

Establish `ih1` using `ih (m + 1) (by omega) (by omega) (T * P) hTP c hc`. Establish `ih0` using `ih m (by omega) (by omega) P hP0 c hc`. Establish `eL : Q.resG k r (Fin.last r) (((qminor (EA hD) (C3.xR k r (m + 2) hm) (C3.xR k r (m + 2) hm) u * P : SA E hD) : Module.End ℂ (VS k r 0 D E)) v₀ : Mx k r → E) c g₀ = Q.resG k r (Fin.last r) (((qminor (EA hD) (C3.xR k r (m + 1) (by omega)) (C3.xR k r (m + 1) (by omega)) u * (T * P) …`. Rewrite using `[resG_last, resG_last, resG_last]`. Establish `key : ∀ (s t : ℂ) (a b d : E), a = b - t • d → s • a = s • b - t • (s • d)`.

Introduce `s t a b d h`. Rewrite using `[h, smul_sub, smul_comm]`. Apply `key` to reduce the goal to its premises. Establish `h2` using `hX`. Simplify using `only [hLaP_apply, La_apply, mul_assoc] at h2`.

Conclude with `h2`. Rewrite using `[eL, ih1, ih0]`. Take `⟨G', hG'def⟩ : ∃ G' : (Fin r → ℂ) → E, G' = resW ((P : Module.End ℂ (VS k r 0 D E)) v₀ : Mx k r → E) g₀` from `⟨_, rfl⟩`. Establish `hG' : G' ∈ WSm r E` using `hG'def ▸ hWS P`. Establish `hGG' : ∀ c' ∈ OmX r, Q.resG k r (Fin.last r) ((P : Module.End ℂ (VS k r 0 D E)) v₀ : Mx k r → E) c' g₀ = G' c'`.

Introduce `c' hc'`. Rewrite using `[hG'def, wsm_resG_eq _ _ hc']`. Establish `hTS : ∀ c' ∈ OmX r, Q.resG k r (Fin.last r) (((T * P : SA E hD) : Module.End ℂ (VS k r 0 D E)) v₀ : Mx k r → E) c' g₀ = (pOp ⟨m + 1, by omega⟩ G' + y • G') c'`. Introduce `c' hc'`. Establish `hts` using `torus_step hD v₀ g₀ y hTC hGP hg₀ hcell hdiff ⟨m + 1, by omega⟩ P c' hc'`.

Rewrite using `[hT, hts, Pi.add_apply, Pi.smul_apply, hGG' c' hc', pOp_locO ⟨m + 1, by omega⟩ (fun c'' hc'' => hGG' c'' hc'') hc', add_comm]`. Rewrite using `[(vAB_loc y (m + 1) _ _ hTS c hc).1, (vAB_loc y m _ _ hGG' c hc).1, (vAB_loc y (m + 2) _ _ hGG' c hc).1]`. Establish `hpG : pOp ⟨m + 1, by omega⟩ G' ∈ WSm r E` using `opL_mem ⟨m + 1, by omega⟩ 0 hG'`. Rewrite using `[(vAB_lin y (m + 1) hpG hG' y).1, (vAB_comm y ⟨m + 1, by omega⟩ (m + 1) le_rfl hG').2.2.1]`. Rewrite using `[(vAB_succ y (m + 1) (by omega) G').1, (vAB_succ y m (by omega) G').2]`.

Simplify using `only [Pi.add_apply, Pi.smul_apply, cOp, ciOp, div_eq_mul_inv, mul_smul]`. Normalize the expressions using the abelian group laws.
-/
theorem claim (hRR : RightRuleE) (hLR : LeftRuleCell) (hTC : TorusCell) (hGP : GaugeP)
    (z z' : Fin (2 * r + k + 1) → ℂ) (hz : inWb k r z) (hz' : inWb k r z')
    (hN : ∀ g ∈ Glev k r 0 ∩ D, ∀ n ∈ Nlev k r 0, n * g ∈ D)
    {f : Mx k r → E} (hf : SmoothLev k r 0 D f) (hLf : LeftEq k r z 0 D f) (hRf : RightEq k r z' 0 D f)
    (hv : v₀ = ⟨cut k r 0 D f, cut_mem hD hf⟩) (hg₀ : g₀ ∈ Glev k r (Fin.last r))
    (hcell : ∀ c ∈ OmX r, wCell k r (Fin.last r) c * g₀ ∈ Glev k r 0 ∩ D)
    (hdiff : ∀ x : SA E hD, ∀ c ∈ OmX r,
      DifferentiableAt ℝ (fun c' => ((x : Module.End ℂ (VS k r 0 D E)) v₀ : Mx k r → E) (wCell k r (Fin.last r) c' * g₀)) c)
    (hWS : ∀ x : SA E hD, resW ((x : Module.End ℂ (VS k r 0 D E)) v₀ : Mx k r → E) g₀ ∈ WSm r E) :
    ∀ (m : ℕ) (hm : m ≤ r), ∀ P ∈ Tor hD m, ∀ c ∈ OmX r,
      Q.resG k r (Fin.last r) (((qminor (EA hD) (C3.xR k r m hm) (C3.xR k r m hm) (y + ((2 * r + k : ℕ) : ℂ) / 2) * P :
          SA E hD) : Module.End ℂ (VS k r 0 D E)) v₀ : Mx k r → E) c g₀ =
        (Q.vAB r y m).1 (fun c' => Q.resG k r (Fin.last r) ((P : Module.End ℂ (VS k r 0 D E)) v₀ : Mx k r → E) c' g₀) c := by
  have hLv : LeftEq k r z 0 D (v₀ : Mx k r → E) := by rw [hv]; exact leftEq_cut z hN hLf
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro hm P hP c hc
  rcases m with _ | _ | m
  · rw [qminor_zero, one_mul]
    rfl
  · rw [qminor_one]
    have hx0 : C3.xR k r 1 hm 0 = eI k r ⟨0, by omega⟩ := by ext; simp [C3.xR, eI]
    have hts := torus_step hD v₀ g₀ y hTC hGP hg₀ hcell hdiff ⟨0, by omega⟩ P c hc
    simp only [Fin.val_mk, Nat.cast_zero, sub_zero] at hts
    rw [hx0, hts, (vAB_succ y 0 (show 0 < r by omega) _).1]
    simp [Q.vAB, cOp]
  · have hm2 : m + 2 ≤ r := hm
    have hP1 : P ∈ Tor hD (m + 1) := Tor_mono hD (by omega) hP
    have hP0 : P ∈ Tor hD m := Tor_mono hD (by omega) hP
    set u : ℂ := y + ((2 * r + k : ℕ) : ℂ) / 2 with hu
    set LaP : SA E hD →ₗ[ℂ] E := (La hD v₀ (wCell k r (Fin.last r) c * g₀)).comp (LinearMap.mulRight ℂ P) with hLaP
    have hLaP_apply : ∀ x, LaP x = La hD v₀ (wCell k r (Fin.last r) c * g₀) (x * P) := fun x => rfl
    have hnot : ∀ (a : ℕ) (ha : a < m + 2), ∀ l' : Fin r, m + 2 ≤ l'.val → eI k r ⟨a, by omega⟩ ≠ eI k r l' := by
      intro a ha l' hl' e
      have := congrArg Fin.val e
      simp [eI] at this
      omega
    have hR0 : ∀ (x : SA E hD) (l : ℕ) (hl : l < m),
        LaP (x * EA hD (eI k r ⟨l, by omega⟩) (eI k r ⟨m + 1, by omega⟩)) = 0 := by
      intro x l hl
      rw [hLaP_apply, mul_assoc, (comm_Tor hD (m + 2) _ _ (hnot l (by omega)) (hnot (m + 1) (by omega)) P hP).eq,
        ← mul_assoc, La_apply, Subalgebra.coe_mul, Module.End.mul_apply]
      conv_lhs => rw [hv]
      rw [root_vector_action_cutoff hD z' hz' hRR hf hRf ⟨l, by omega⟩ ⟨m + 1, by omega⟩ (by simp; omega), if_neg (by simp; omega),
        zero_smul, map_zero]
      rfl
    have hR1 : ∀ x : SA E hD, LaP (x * EA hD (eI k r ⟨m, by omega⟩) (eI k r ⟨m + 1, by omega⟩)) = LaP x := by
      intro x
      rw [hLaP_apply, hLaP_apply, mul_assoc, (comm_Tor hD (m + 2) _ _ (hnot m (by omega)) (hnot (m + 1) (by omega)) P hP).eq,
        ← mul_assoc, La_apply, La_apply, Subalgebra.coe_mul, Module.End.mul_apply]
      conv_lhs => rw [hv]
      rw [root_vector_action_cutoff hD z' hz' hRR hf hRf ⟨m, by omega⟩ ⟨m + 1, by omega⟩ (by simp), if_pos (by simp), one_smul, ← hv]
    have hL : ∀ (x : SA E hD) (q : ℕ) (hq : q ≤ m),
        LaP (EA hD (eI k r ⟨m + 1, by omega⟩) (eI k r ⟨q, by omega⟩) * x) =
          (if q = m then c ⟨m + 1, by omega⟩ / c ⟨m, by omega⟩ else 0) • LaP x := by
      intro x q hq
      rw [hLaP_apply, hLaP_apply, mul_assoc, La_apply, La_apply, Subalgebra.coe_mul, Module.End.mul_apply, EA_val,
        ev_E hD _ _ _ (hcell c hc), posL_cI, posL_cI]
      have hsm := (((x * P : SA E hD) : Module.End ℂ (VS k r 0 D E)) v₀).2.1
      have hle := leftEq_SA hD z hN (x * P) v₀ hLv
      rw [hLR E k r z D _ hz hD hN hsm hle c hc g₀ hg₀ (hcell c hc).2 ⟨m + 1, by omega⟩ ⟨q, by omega⟩ (by simp; omega)]
      congr 1
      by_cases hqm : q = m
      · subst hqm
        simp
      · rw [if_neg (by simp; omega), if_neg hqm]
    have hX := Formalism.FourierDecayAlt.P.PBN.chainX1' k r c (EA (E := E) hD) LaP (EA_gl (E := E) hD) m hm2 u hR0 hR1 hL

    set T := Tm (EA (E := E) hD) (u - ((m + 1 : ℕ) : ℂ)) (eI k r ⟨m + 1, by omega⟩) (eI k r ⟨m + 1, by omega⟩) with hT
    have hTmem : T ∈ Tor hD (m + 1) := by
      rw [hT]
      unfold Tm
      rw [if_pos rfl]
      exact Subalgebra.add_mem _ (Subalgebra.algebraMap_mem _ _) (EA_mem_Tor hD ⟨m + 1, by omega⟩ le_rfl)
    have hTP : T * P ∈ Tor hD (m + 1) := Subalgebra.mul_mem _ hTmem hP1
    have ih1 := ih (m + 1) (by omega) (by omega) (T * P) hTP c hc
    have ih0 := ih m (by omega) (by omega) P hP0 c hc

    have eL : Q.resG k r (Fin.last r) (((qminor (EA hD) (C3.xR k r (m + 2) hm) (C3.xR k r (m + 2) hm) u * P :
        SA E hD) : Module.End ℂ (VS k r 0 D E)) v₀ : Mx k r → E) c g₀ =
        Q.resG k r (Fin.last r) (((qminor (EA hD) (C3.xR k r (m + 1) (by omega)) (C3.xR k r (m + 1) (by omega)) u *
          (T * P) : SA E hD) : Module.End ℂ (VS k r 0 D E)) v₀ : Mx k r → E) c g₀ -
        (c ⟨m + 1, by omega⟩ / c ⟨m, by omega⟩) • Q.resG k r (Fin.last r)
          (((qminor (EA hD) (C3.xR k r m (by omega)) (C3.xR k r m (by omega)) u * P : SA E hD) :
            Module.End ℂ (VS k r 0 D E)) v₀ : Mx k r → E) c g₀ := by
      rw [resG_last, resG_last, resG_last]
      have key : ∀ (s t : ℂ) (a b d : E), a = b - t • d → s • a = s • b - t • (s • d) := by
        intro s t a b d h
        rw [h, smul_sub, smul_comm]
      apply key
      have h2 := hX
      simp only [hLaP_apply, La_apply, mul_assoc] at h2
      exact h2
    rw [eL, ih1, ih0]

    obtain ⟨G', hG'def⟩ : ∃ G' : (Fin r → ℂ) → E,
        G' = resW ((P : Module.End ℂ (VS k r 0 D E)) v₀ : Mx k r → E) g₀ := ⟨_, rfl⟩
    have hG' : G' ∈ WSm r E := hG'def ▸ hWS P
    have hGG' : ∀ c' ∈ OmX r,
        Q.resG k r (Fin.last r) ((P : Module.End ℂ (VS k r 0 D E)) v₀ : Mx k r → E) c' g₀ = G' c' := by
      intro c' hc'
      rw [hG'def, wsm_resG_eq _ _ hc']
    have hTS : ∀ c' ∈ OmX r,
        Q.resG k r (Fin.last r) (((T * P : SA E hD) : Module.End ℂ (VS k r 0 D E)) v₀ : Mx k r → E) c' g₀ =
          (pOp ⟨m + 1, by omega⟩ G' + y • G') c' := by
      intro c' hc'
      have hts := torus_step hD v₀ g₀ y hTC hGP hg₀ hcell hdiff ⟨m + 1, by omega⟩ P c' hc'
      rw [hT, hts, Pi.add_apply, Pi.smul_apply, hGG' c' hc',
        pOp_locO ⟨m + 1, by omega⟩ (fun c'' hc'' => hGG' c'' hc'') hc', add_comm]
    rw [(vAB_loc y (m + 1) _ _ hTS c hc).1, (vAB_loc y m _ _ hGG' c hc).1, (vAB_loc y (m + 2) _ _ hGG' c hc).1]
    have hpG : pOp ⟨m + 1, by omega⟩ G' ∈ WSm r E := opL_mem ⟨m + 1, by omega⟩ 0 hG'
    rw [(vAB_lin y (m + 1) hpG hG' y).1, (vAB_comm y ⟨m + 1, by omega⟩ (m + 1) le_rfl hG').2.2.1]
    rw [(vAB_succ y (m + 1) (by omega) G').1, (vAB_succ y m (by omega) G').2]
    simp only [Pi.add_apply, Pi.smul_apply, cOp, ciOp, div_eq_mul_inv, mul_smul]
    abel

end claim2

end Formalism.FourierDecayAlt.P.PBN.MC
