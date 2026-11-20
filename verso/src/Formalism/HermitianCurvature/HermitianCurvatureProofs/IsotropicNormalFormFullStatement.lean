import Formalism.HermitianCurvature.HermitianCurvatureProofs.HermitianPerturbedVectorOrthogonal

open Matrix Finset

namespace Formalism.FourierDecayAlt.P.SignAntidiagonal

open Formalism.FourierDecayAlt.C3 Formalism.QuantumDeterminants

noncomputable section

/- English proof (translation)
Introduce `k m z' i y t hz hZ ht hyi hyi2 hdet hzy hzyi hiso`. Establish `hiv` using `i.isLt`. Use `set Y' : Matrix (Fin m) (Fin m) ℂ := Matrix.of fun a b : Fin m => y (i.succAbove a) (esI k (m + 1) (i.succAbove b)) with hY'`. Establish `hu : IsUnit Y'.det` using `isUnit_iff_ne_zero.mpr hdet`. Take `⟨N, hN⟩ : ∃ N, N = Y'⁻¹` from `⟨_, rfl⟩`.

Establish `hNY : N * Y' = 1` using `by rw [hN]; exact Matrix.nonsing_inv_mul _ hu`. Establish `hYN : Y' * N = 1` using `by rw [hN]; exact Matrix.mul_nonsing_inv _ hu`. Use `set Vc : Fin m → Fin (2 * (m + 1) + k + 1) → ℂ := fun b => ∑ a, N b a • y (i.succAbove a) with hVcdef`. Establish `hsne : ∀ b : Fin m, (i.succAbove b).val ≠ i.val` using `fun b h' => Fin.succAbove_ne i b (Fin.ext h')`. Establish `hVs : ∀ (b : Fin m) (q : Fin (2 * (m + 1) + k + 1)), m + 1 + k < q.val → Vc b q = if (NFOne.sg k (m + 1) q).val = (i.succAbove b).val then 1 else 0`.

Introduce `b q hq`. Establish `hqv` using `q.isLt`. Simplify using `only [Vc, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]`. Distinguish the cases in `hqi : (NFOne.sg k (m + 1) q).val = i.val`. Establish `hq' : q = esI k (m + 1) i` using `by ext; rw [sg_val'] at hqi; simp [esI]; omega`.

Rewrite using `[if_neg (by rw [hqi]; exact (hsne b).symm)]`. Apply `Finset.sum_eq_zero` to reduce the goal to its premises. Introduce `a _`. Rewrite using `[hq', hyi _ (Fin.succAbove_ne i a), mul_zero]`. Establish `hc : (NFOne.sg k (m + 1) q).val < m + 1 ∧ (NFOne.sg k (m + 1) q).val ≠ i.val` using `⟨by rw [sg_val']; omega, hqi⟩ set b'' := pidx m i _ hc with hb''`.

Establish `hq' : q = esI k (m + 1) (i.succAbove b'')` using `by ext; have := succAbove_pidx m i _ hc; rw [← hb''] at this; rw [sg_val'] at this; simp [esI]; omega`. Establish `e` using `congrFun (congrFun hNY b) b''`. Rewrite `e` using `[Matrix.mul_apply, Matrix.one_apply]`. Use `conv_lhs => rw [hq']`. Simplify using `only [hY', Matrix.of_apply] at e`.

Rewrite using `[e]`. Establish `hsb` using `succAbove_pidx m i _ hc`. Rewrite `hsb` using `[← hb'']`. Distinguish the cases in `hbb : b = b''`. Rewrite using `[if_pos hbb, if_pos (by rw [hbb]; exact hsb.symm)]`.

Rewrite using `[if_neg hbb, if_neg]`. Introduce `h'`. Apply `hbb` to reduce the goal to its premises. Establish `: i.succAbove b = i.succAbove b''` using `by ext; rw [← h', hsb]`. Conclude with `Fin.succAbove_right_injective this`.

Use `set V1 : ℕ → Fin (2 * (m + 1) + k + 1) → ℂ := fun c => if hc : c < m + 1 ∧ c ≠ i.val then Vc (pidx m i c hc) else if c = i.val then ViF m i Vc else 0 with hV1def`. Establish `hV1c : ∀ b : Fin m, V1 (i.succAbove b).val = Vc b`. Introduce `b`. Simplify using `only [V1]`. Rewrite using `[dif_pos ⟨(i.succAbove b).isLt, hsne b⟩, pidx_succAbove]`.

Establish `hV1i : V1 i.val = ViF m i Vc`. Simplify using `[V1]`. Establish `hyy' : ∀ a a' : Fin m, herm (Hpk k (m + 1)) (y (i.succAbove a)) (y (i.succAbove a')) = 0` using `fun a a' => hiso _ _`. Establish `hVciso : ∀ b c : Fin m, herm (Hpk k (m + 1)) (Vc b) (Vc c) = 0` using `fun b c => NFOne.herm_comb k (m + 1) m (fun a => y (i.succAbove a)) hyy' _ _`. Establish `V1_0 : ∀ c, m + 1 ≤ c → V1 c = 0`.

Introduce `c hc; simp only [V1]; rw [dif_neg (by omega), if_neg (by omega)]`. Establish `V1_cases : ∀ c, c < m + 1 → (c = i.val ∧ V1 c = ViF m i Vc) ∨ (∃ b : Fin m, (i.succAbove b).val = c ∧ V1 c = Vc b)`. Introduce `c hc`. Distinguish the cases in `hci : c = i.val`. Use the proof step `left; exact ⟨hci, by rw [hci, hV1i]⟩`.

Use `right`. Use `⟨pidx m i c ⟨hc, hci⟩, succAbove_pidx m i c ⟨hc, hci⟩, ?_⟩` and prove the remaining obligations. Simplify using `only [V1]`. Rewrite using `[dif_pos ⟨hc, hci⟩]`. Establish `V1_s : ∀ b, b < m + 1 → ∀ q : Fin (2 * (m + 1) + k + 1), m + 1 + k < q.val → V1 b q = if (NFOne.sg k (m + 1) q).val = b then 1 else 0`.

Introduce `b hb q hq`. Break down `V1_cases b hb with ⟨hbi, hv⟩ | ⟨b', hb', hv⟩` into its components or cases. Rewrite using `[hv, ViF_star m i Vc q hq, hbi]`. Rewrite using `[hv, hVs b' q hq, hb']`. Establish `V1_iso : ∀ b c, b < m + 1 → c < m + 1 → herm (Hpk k (m + 1)) (V1 b) (V1 c) = 0`.

Introduce `b c hb hc`. Apply the tactic sequence `rcases V1_cases b hb with ⟨_, hv⟩ | ⟨b', _, hv⟩ <;> rcases V1_cases c hc with ⟨_, hw⟩ | ⟨c', _, hw⟩ <;> rw [hv, hw]`. Conclude with `ViF_iso m i Vc`. Conclude with `ViF_Vc m i Vc hVs c'`. Rewrite using `[herm_swap, ViF_Vc m i Vc hVs b', star_zero]`.

Conclude with `hVciso b' c'`. Establish `V1_z : ∀ c, herm (Hpk k (m + 1)) z' (V1 c) = 0`. Introduce `c`. Distinguish the cases in `hc : c < m + 1`. Apply the tactic sequence `rcases V1_cases c hc with ⟨_, hv⟩ | ⟨b', _, hv⟩ <;> rw [hv]`.

Conclude with `hermitian_insertion_vector_orthogonal m i Vc z' hz`. Conclude with `NFOne.herm_Hpk_of_inWb_eq_sum_wI k (m + 1) m (fun a => y (i.succAbove a)) z' (fun a => hzy _ (Fin.succAbove_ne i a)) _`. Rewrite using `[V1_0 c (by omega)]; simp [herm]`. Establish `hn1` using `one_add_projection_mem_isotropic_set (m + 1) z' hz V1 V1_0 V1_s V1_iso V1_z`. Use `set n1 := 1 + NFOne.Pm k (m + 1) (m + 1) V1 with hn1def`.

Establish `hn1col : ∀ b : Fin (m + 1), n1 *ᵥ bvec (esI k (m + 1) b) = V1 b.val` using `fun b => pm_col_star (m + 1) V1 V1_s b b.isLt`. Establish `hU1 : IsUnit n1.det` using `WeylGroupFacts.isUnit_of_uh hn1.1`. Use `set u := n1⁻¹ *ᵥ y i with hudef`. Establish `hnu : n1 *ᵥ u = y i` using `by rw [hudef, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hU1, Matrix.one_mulVec]`. Establish `hpres` using `herm_unitary n1 hn1.1`.

Establish `u_star : ∀ p : Fin (2 * (m + 1) + k + 1), m + 1 + k < p.val → u p = 0`. Introduce `p hp`. Establish `hpv` using `p.isLt`. Establish `hpe : p = esI k (m + 1) ⟨2 * (m + 1) + k - p.val, by omega⟩` using `by ext; simp [esI]; omega`. Establish `e` using `herm_bvec_eI (k := k) u (⟨2 * (m + 1) + k - p.val, by omega⟩ : Fin (m + 1))`.

Rewrite using `[hpe, ← e, ← hpres, hnu, hn1.2.1, herm_bvec_eI]`. Conclude with `hyi2 _ (by simp [esI]; omega)`. Establish `u_X : ∀ c : Fin (m + 1), c ≠ i → u (eI k (m + 1) c) = 0`. Introduce `c hc`. Establish `e` using `herm_bvec_esI (k := k) u c`.

Rewrite using `[← e, ← hpres, hnu, hn1col c]`. Break down `V1_cases c.val c.isLt with ⟨hci, _⟩ | ⟨b', _, hv⟩` into its components or cases. Conclude with `absurd (Fin.ext hci) hc`. Rewrite using `[hv]`. Conclude with `NFOne.herm_Hpk_of_inWb_eq_sum_wI k (m + 1) m (fun a => y (i.succAbove a)) (y i) (fun a => hiso _ _) _`.

Use `set β := u (eI k (m + 1) i) with hβ`. Use `set yb : Fin (2 * (m + 1) + k + 1) → ℂ := fun p => if m + 1 ≤ p.val ∧ p.val ≤ m + 1 + k then u p else 0 with hybdef`. Establish `hyb : inWb k (m + 1) yb` using `by intro p hp; simp only [yb]; rw [if_neg (by omega)]`. Establish `u_dec : u = fun p => yb p + β * bvec (eI k (m + 1) i) p`. Use function extensionality and compare the values at `p`.

Simplify using `only [yb]`. Distinguish the cases in `hW : m + 1 ≤ p.val ∧ p.val ≤ m + 1 + k`. Establish `: p ≠ eI k (m + 1) i` using `by intro h; rw [h] at hW; simp [eI] at hW; omega`. Simplify using `[hW, bvec, Pi.single_apply, this]`. Rewrite using `[if_neg hW, zero_add]`.

Distinguish the cases in `hX : p.val < m + 1`. Distinguish the cases in `hpi : p.val = i.val`. Establish `: p = eI k (m + 1) i` using `by ext; simp [eI, hpi]`. Rewrite using `[this]`. Simplify using `[bvec, hβ]`.

Establish `hpe : p = eI k (m + 1) ⟨p.val, hX⟩` using `by ext; simp [eI]`. Establish `hne : (⟨p.val, hX⟩ : Fin (m + 1)) ≠ i` using `by intro h; apply hpi; rw [← h]`. Establish `hne2 : p ≠ eI k (m + 1) i` using `by intro h; apply hpi; rw [h]; simp [eI]`. Rewrite using `[hpe, u_X _ hne]`. Simplify using `[bvec, Pi.single_apply, ← hpe, hne2]`.

Establish `hne2 : p ≠ eI k (m + 1) i` using `by intro h; apply hX; rw [h]; simp only [eI]; omega`. Rewrite using `[u_star p (by omega)]; simp [bvec, Pi.single_apply, hne2]`. Establish `tau_W : ∀ l : Fin (2 * (m + 1) + k + 1), m + 1 ≤ l.val ∧ l.val ≤ m + 1 + k → WeylGroupFacts.tau k (m + 1) l = l`. Apply the tactic sequence `intro l hl; ext; rw [tau_val]; split_ifs <;> omega`. Establish `tau_notW : ∀ l : Fin (2 * (m + 1) + k + 1), ¬ (m + 1 ≤ l.val ∧ l.val ≤ m + 1 + k) → (WeylGroupFacts.tau k (m + 1) l).val < m + 1 ∨ m + 1 + k < (WeylGroupFacts.tau k (m + 1) l).val`.

Apply the tactic sequence `intro l hl; rw [tau_val]; split_ifs <;> omega`. Establish `yb_iso : herm (Hpk k (m + 1)) yb yb = 0`. Establish `: herm (Hpk k (m + 1)) yb yb = herm (Hpk k (m + 1)) u u`. Rewrite using `[herm_expand, herm_expand]`. Use `Finset.sum_congr rfl (fun l _ => ?_)` and prove the remaining obligations.

Distinguish the cases in `hW : m + 1 ≤ l.val ∧ l.val ≤ m + 1 + k`. Rewrite using `[tau_W l hW]`. Simplify using `only [yb, if_pos hW]`. Establish `h1 : yb l = 0` using `by simp only [yb, if_neg hW]`. Rewrite using `[h1]`.

Distinguish the cases in `hX : l.val < m + 1`. Apply the tactic sequence `rw [u_star (WeylGroupFacts.tau k (m + 1) l) (by rw [tau_val]; split_ifs <;> omega)]; simp`. Rewrite using `[u_star l (by omega)]; simp`. Rewrite using `[this, ← hpres, hnu, hiso]`. Establish `yb_z : herm (Hpk k (m + 1)) z' yb = t`.

Establish `: herm (Hpk k (m + 1)) z' yb = herm (Hpk k (m + 1)) z' u`. Rewrite using `[herm_expand, herm_expand]`. Use `Finset.sum_congr rfl (fun l _ => ?_)` and prove the remaining obligations. Distinguish the cases in `hW : m + 1 ≤ l.val ∧ l.val ≤ m + 1 + k`. Simplify using `only [yb, if_pos hW]`.

Rewrite using `[hz (WeylGroupFacts.tau k (m + 1) l) (tau_notW l hW)]`. Simplify using the standard rewrite rules. Rewrite using `[this, ← hpres, hnu, hn1.2.2.1, hzyi]`. Use `set Z := herm (Hpk k (m + 1)) z' z' with hZdef`. Use `set c2 : ℂ := star (β / star t) with hc2`.

Use `set c1 : ℂ := star (-(β / star t) * Z / t) with hc1`. Use `set ν : Fin (2 * (m + 1) + k + 1) → ℂ := c1 • yb + c2 • z' with hνdef`. Establish `hst : star t ≠ 0` using `star_ne_zero.mpr ht`. Establish `hν : inWb k (m + 1) ν`. Introduce `p hp`.

Simplify using `only [ν, Pi.add_apply, Pi.smul_apply, hyb p hp, hz p hp, smul_zero, add_zero]`. Establish `hzν : herm (Hpk k (m + 1)) z' ν = 0`. Rewrite using `[hνdef, herm_add_smul_right, yb_z, hc1, hc2, star_star, star_star]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.

Establish `hybν : herm (Hpk k (m + 1)) yb ν = β`. Rewrite using `[hνdef, herm_add_smul_right, yb_iso, herm_swap k (m + 1) yb z', yb_z]`. Simplify using `only [hc2, star_star, mul_zero, zero_add]`. Clear the denominators using the available nonvanishing facts. Use `set V2 : ℕ → Fin (2 * (m + 1) + k + 1) → ℂ := fun c => if hc : c < m + 1 then (if c = i.val then VpF m i ν else bvec (esI k (m + 1) ⟨c, hc⟩)) else 0 with hV2def`.

Establish `V2_cases : ∀ c (hc : c < m + 1), (c = i.val ∧ V2 c = VpF m i ν) ∨ (c ≠ i.val ∧ V2 c = bvec (esI k (m + 1) ⟨c, hc⟩))`. Introduce `c hc`. Distinguish the cases in `hci : c = i.val`. Use `left`. Use `⟨hci, ?_⟩` and prove the remaining obligations.

Simplify using `only [V2]`. Rewrite using `[dif_pos hc, if_pos hci]`. Use `right`. Use `⟨hci, ?_⟩` and prove the remaining obligations. Simplify using `only [V2]`.

Rewrite using `[dif_pos hc, if_neg hci]`. Establish `V2_0 : ∀ c, m + 1 ≤ c → V2 c = 0` using `by intro c hc; simp only [V2]; rw [dif_neg (by omega)]`. Establish `V2_s : ∀ b, b < m + 1 → ∀ q : Fin (2 * (m + 1) + k + 1), m + 1 + k < q.val → V2 b q = if (NFOne.sg k (m + 1) q).val = b then 1 else 0`. Introduce `b hb q hq`. Break down `V2_cases b hb with ⟨hbi, hv⟩ | ⟨_, hv⟩` into its components or cases.

Rewrite using `[hv, VpF_star m i ν hν q hq, hbi]`. Rewrite using `[hv, bvec_esI_star]`. Establish `V2_iso : ∀ b c, b < m + 1 → c < m + 1 → herm (Hpk k (m + 1)) (V2 b) (V2 c) = 0`. Introduce `b c hb hc`. Apply the tactic sequence `rcases V2_cases b hb with ⟨hbi, hv⟩ | ⟨hbi, hv⟩ <;> rcases V2_cases c hc with ⟨hci, hw⟩ | ⟨hci, hw⟩ <;> rw [hv, hw]`.

Conclude with `VpF_iso m i ν hν`. Conclude with `VpF_esI m i ν hν _ (by intro h; apply hci; rw [← h])`. Rewrite using `[herm_swap, VpF_esI m i ν hν _ (by intro h; apply hbi; rw [← h]), star_zero]`. Conclude with `bvec_esI_iso m _ _`. Establish `V2_z : ∀ c, herm (Hpk k (m + 1)) z' (V2 c) = 0`.

Introduce `c`. Distinguish the cases in `hc : c < m + 1`. Apply the tactic sequence `rcases V2_cases c hc with ⟨_, hv⟩ | ⟨_, hv⟩ <;> rw [hv]`. Conclude with `hermitian_perturbed_vector_orthogonal m i ν z' hz hν hzν`. Rewrite using `[herm_bvec_esI]; exact hz _ (Or.inl (by simp only [eI]; omega))`.

Rewrite using `[V2_0 c (by omega)]; simp [herm]`. Establish `hn2` using `one_add_projection_mem_isotropic_set (m + 1) z' hz V2 V2_0 V2_s V2_iso V2_z`. Use `set n2 := 1 + NFOne.Pm k (m + 1) (m + 1) V2 with hn2def`. Establish `hn2col : ∀ b : Fin (m + 1), n2 *ᵥ bvec (esI k (m + 1) b) = V2 b.val` using `fun b => pm_col_star (m + 1) V2 V2_s b b.isLt`. Establish `hn2yb : n2 *ᵥ yb = u`.

Rewrite using `[u_dec, hn2def, Matrix.add_mulVec, Matrix.one_mulVec]`. Use function extensionality and compare the values at `p`. Rewrite using `[Pi.add_apply]`. Use `congr 1`. Simplify using `only [Matrix.mulVec, dotProduct]`.

Distinguish the cases in `hp : p.val < m + 1`. Establish `hterm : ∀ q, NFOne.Pm k (m + 1) (m + 1) V2 p q * yb q = if p.val = i.val then star (ν q) * (WeylGroupFacts.sgn k (m + 1) q * yb (WeylGroupFacts.tau k (m + 1) q)) else 0`. Introduce `q`. Distinguish the cases in `hW : m + 1 ≤ q.val ∧ q.val ≤ m + 1 + k`. Rewrite using `[NFOne.P_XW k (m + 1) (m + 1) V2 p q hp hW.1 hW.2, tau_W q hW]`.

Establish `hdW : NFOne.dW k (m + 1) q = WeylGroupFacts.sgn k (m + 1) q` using `rfl`. Break down `V2_cases p.val hp with ⟨hpi, hv⟩ | ⟨hpi, hv⟩` into its components or cases. Rewrite using `[hv, if_pos hpi]`. Unfold `VpF`. Establish `h1 : q ≠ esI k (m + 1) i` using `by intro h; rw [h] at hW; simp [esI] at hW; omega`.

Establish `h2 : q ≠ eI k (m + 1) i` using `by intro h; rw [h] at hW; simp [eI] at hW; omega`. Simplify using `only [bvec, Pi.single_apply, if_neg h1, if_neg h2, hdW]`. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hv, if_neg hpi]`.

Establish `h1 : q ≠ esI k (m + 1) ⟨p.val, hp⟩` using `by intro h; rw [h] at hW; simp [esI] at hW; omega`. Simplify using `[bvec, Pi.single_apply, h1]`. Establish `h0 : yb q = 0` using `hyb q (by omega)`. Rewrite using `[h0, mul_zero]`. Use `split_ifs`.

Rewrite using `[hyb (WeylGroupFacts.tau k (m + 1) q) (tau_notW q hW)]`. Simplify using the standard rewrite rules. Both sides reduce to the same expression. Rewrite using `[Finset.sum_congr rfl (fun q _ => hterm q)]`. Distinguish the cases in `hpi : p.val = i.val`.

Simplify using `only [if_pos hpi]`. Rewrite using `[← herm_expand, hybν]`. Establish `: p = eI k (m + 1) i` using `by ext; simp [eI, hpi]`. Simplify using `[bvec, this]`. Establish `: p ≠ eI k (m + 1) i` using `by intro h; apply hpi; rw [h]; simp [eI]`.

Simplify using `[hpi, bvec, Pi.single_apply, this]`. Establish `: p ≠ eI k (m + 1) i` using `by intro h; apply hp; rw [h]; simp only [eI]; omega`. Rewrite using `[Finset.sum_eq_zero]`. Simplify using `[bvec, Pi.single_apply, this]`. Introduce `q _`.

Distinguish the cases in `hW : m + 1 ≤ q.val ∧ q.val ≤ m + 1 + k`. Rewrite using `[NFOne.P_rowWS_colW k (m + 1) (m + 1) V2 p q (by omega) hW.2, zero_mul]`. Rewrite using `[hyb q (by omega), mul_zero]`. Use `set ystar : Fin (m + 1) → Fin (2 * (m + 1) + k + 1) → ℂ := fun a p => if m + 1 + k < p.val then y a p else 0 with hystar`. Establish `hdec : ∀ a'' : Fin m, ystar (i.succAbove a'') = ∑ b : Fin m, Y' a'' b • bvec (esI k (m + 1) (i.succAbove b))`.

Introduce `a''`. Use function extensionality and compare the values at `p`. Simplify using `only [ystar, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, bvec, Pi.single_apply]`. Distinguish the cases in `hp : m + 1 + k < p.val`. Rewrite using `[if_pos hp]`.

Establish `hpv` using `p.isLt`. Distinguish the cases in `hpi : (NFOne.sg k (m + 1) p).val = i.val`. Establish `hpe : p = esI k (m + 1) i` using `by ext; rw [sg_val'] at hpi; simp [esI]; omega`. Rewrite using `[hpe, hyi _ (Fin.succAbove_ne i a'')]`. Use `symm`.

Apply `Finset.sum_eq_zero` to reduce the goal to its premises. Introduce `b _`. Rewrite using `[if_neg, mul_zero]`. Introduce `h`. Use `congrArg Fin.val h` as an intermediate fact.

Simplify using `[esI] at this`. Conclude with `hsne b (by have := (i.succAbove b).isLt; omega)`. Establish `hc : (NFOne.sg k (m + 1) p).val < m + 1 ∧ (NFOne.sg k (m + 1) p).val ≠ i.val` using `⟨by rw [sg_val']; omega, hpi⟩`. Establish `hsb` using `succAbove_pidx m i _ hc`. Establish `hsv : (NFOne.sg k (m + 1) p).val = 2 * (m + 1) + k - p.val` using `sg_val' m p`.

Establish `hpe : p = esI k (m + 1) (i.succAbove (pidx m i _ hc))` using `by ext; show p.val = 2 * (m + 1) + k - (i.succAbove (pidx m i _ hc)).val; rw [hsb, hsv]; omega`. Rewrite using `[Finset.sum_eq_single (pidx m i _ hc)]`. Rewrite using `[if_pos hpe, mul_one]`. Conclude with `congrArg (y (i.succAbove a'')) hpe`. Introduce `b _ hb`.

Rewrite using `[if_neg, mul_zero]`. Introduce `h`. Apply `hb` to reduce the goal to its premises. Rewrite `h` using `[hpe]`. Establish `hv` using `congrArg Fin.val h`.

Simplify using `only [esI] at hv`. Establish `h2 : i.succAbove (pidx m i _ hc) = i.succAbove b` using `by ext; have h3 := (i.succAbove b).isLt; have h4 := (i.succAbove (pidx m i _ hc)).isLt; omega`. Conclude with `(Fin.succAbove_right_injective h2).symm`. Simplify using the standard rewrite rules. Rewrite using `[if_neg hp] symm`.

Apply `Finset.sum_eq_zero` to reduce the goal to its premises. Introduce `b _`. Rewrite using `[if_neg, mul_zero]`. Introduce `h`. Apply `hp` to reduce the goal to its premises.

Rewrite using `[h]`. Simplify using `[esI]`. Use `(i.succAbove b).isLt` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Establish `hn1y : ∀ a'' : Fin m, n1 *ᵥ ystar (i.succAbove a'') = y (i.succAbove a'')`.

Introduce `a''`. Rewrite using `[hdec, Matrix.mulVec_sum]`. Simplify using `only [Matrix.mulVec_smul, hn1col, hV1c, Vc, Finset.smul_sum, smul_smul]`. Rewrite using `[Finset.sum_comm]`. Simplify using `only [← Finset.sum_smul]`.

Rewrite using `[Finset.sum_eq_single a'']`. Use `congrFun (congrFun hYN a'') a''` as an intermediate fact. Rewrite `this` using `[Matrix.mul_apply, Matrix.one_apply, if_pos rfl]`. Rewrite using `[this, one_smul]`. Introduce `a' _ ha'`.

Use `congrFun (congrFun hYN a'') a'` as an intermediate fact. Rewrite `this` using `[Matrix.mul_apply, Matrix.one_apply, if_neg (Ne.symm ha')]`. Rewrite using `[this, zero_smul]`. Simplify using the standard rewrite rules. Establish `hn2y : ∀ a'' : Fin m, n2 *ᵥ ystar (i.succAbove a'') = ystar (i.succAbove a'')`.

Introduce `a''`. Rewrite using `[hdec, Matrix.mulVec_sum]`. Simplify using `only [Matrix.mulVec_smul, hn2col]`. Use `Finset.sum_congr rfl (fun b _ => ?_)` and prove the remaining obligations. Break down `V2_cases (i.succAbove b).val (i.succAbove b).isLt with ⟨hbi, _⟩ | ⟨_, hv⟩` into its components or cases.

Conclude with `absurd hbi (hsne b)`. Rewrite using `[hv]`. Use `⟨n1 * n2, mul_mem_isotropic_unipotent_set z' (m + 1) (m + 1) V1 V2 hn1 hn2, fun a => if a = i then yb else ystar a, fun a => ?_⟩` and prove the remaining obligations. Distinguish the cases in `ha : a = i`. Substitute `ha` using the available equality.

Simplify using `only [if_true]`. Use `⟨by rw [← Matrix.mulVec_mulVec, hn2yb, hnu], fun h => absurd rfl h, fun _ => ⟨hyb, yb_z⟩⟩` and prove the remaining obligations. Simplify using `only [if_neg ha]`. Take `⟨a'', rfl⟩` from `Fin.exists_succAbove_eq ha`. Use `⟨by rw [← Matrix.mulVec_mulVec, hn2y, hn1y], fun _ => ⟨?_, ?_⟩, fun h => absurd h ha⟩` and prove the remaining obligations.

Introduce `p hp; simp only [ystar]; rw [if_neg (by omega)]`. Introduce `p hp`. Simplify using `only [ystar]`. Rewrite using `[if_pos hp]`.
-/
theorem isotropicNormalFormFull_statement : IsotropicNormalFormFull := by
  intro k m z' i y t hz hZ ht hyi hyi2 hdet hzy hzyi hiso
  have hiv := i.isLt

  set Y' : Matrix (Fin m) (Fin m) ℂ :=
    Matrix.of fun a b : Fin m => y (i.succAbove a) (esI k (m + 1) (i.succAbove b)) with hY'
  have hu : IsUnit Y'.det := isUnit_iff_ne_zero.mpr hdet
  obtain ⟨N, hN⟩ : ∃ N, N = Y'⁻¹ := ⟨_, rfl⟩
  have hNY : N * Y' = 1 := by rw [hN]; exact Matrix.nonsing_inv_mul _ hu
  have hYN : Y' * N = 1 := by rw [hN]; exact Matrix.mul_nonsing_inv _ hu
  set Vc : Fin m → Fin (2 * (m + 1) + k + 1) → ℂ := fun b => ∑ a, N b a • y (i.succAbove a) with hVcdef
  have hsne : ∀ b : Fin m, (i.succAbove b).val ≠ i.val := fun b h' => Fin.succAbove_ne i b (Fin.ext h')
  have hVs : ∀ (b : Fin m) (q : Fin (2 * (m + 1) + k + 1)), m + 1 + k < q.val →
      Vc b q = if (NFOne.sg k (m + 1) q).val = (i.succAbove b).val then 1 else 0 := by
    intro b q hq
    have hqv := q.isLt
    simp only [Vc, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    by_cases hqi : (NFOne.sg k (m + 1) q).val = i.val
    · have hq' : q = esI k (m + 1) i := by ext; rw [sg_val'] at hqi; simp [esI]; omega
      rw [if_neg (by rw [hqi]; exact (hsne b).symm)]
      apply Finset.sum_eq_zero; intro a _
      rw [hq', hyi _ (Fin.succAbove_ne i a), mul_zero]
    · have hc : (NFOne.sg k (m + 1) q).val < m + 1 ∧ (NFOne.sg k (m + 1) q).val ≠ i.val := ⟨by rw [sg_val']; omega, hqi⟩
      set b'' := pidx m i _ hc with hb''
      have hq' : q = esI k (m + 1) (i.succAbove b'') := by
        ext; have := succAbove_pidx m i _ hc; rw [← hb''] at this; rw [sg_val'] at this; simp [esI]; omega
      have e := congrFun (congrFun hNY b) b''
      rw [Matrix.mul_apply, Matrix.one_apply] at e
      conv_lhs => rw [hq']
      simp only [hY', Matrix.of_apply] at e
      rw [e]
      have hsb := succAbove_pidx m i _ hc
      rw [← hb''] at hsb
      by_cases hbb : b = b''
      · rw [if_pos hbb, if_pos (by rw [hbb]; exact hsb.symm)]
      · rw [if_neg hbb, if_neg]
        intro h'; apply hbb
        have : i.succAbove b = i.succAbove b'' := by ext; rw [← h', hsb]
        exact Fin.succAbove_right_injective this
  set V1 : ℕ → Fin (2 * (m + 1) + k + 1) → ℂ := fun c =>
    if hc : c < m + 1 ∧ c ≠ i.val then Vc (pidx m i c hc) else if c = i.val then ViF m i Vc else 0 with hV1def
  have hV1c : ∀ b : Fin m, V1 (i.succAbove b).val = Vc b := by
    intro b
    simp only [V1]
    rw [dif_pos ⟨(i.succAbove b).isLt, hsne b⟩, pidx_succAbove]
  have hV1i : V1 i.val = ViF m i Vc := by
    simp [V1]
  have hyy' : ∀ a a' : Fin m, herm (Hpk k (m + 1)) (y (i.succAbove a)) (y (i.succAbove a')) = 0 :=
    fun a a' => hiso _ _
  have hVciso : ∀ b c : Fin m, herm (Hpk k (m + 1)) (Vc b) (Vc c) = 0 :=
    fun b c => NFOne.herm_comb k (m + 1) m (fun a => y (i.succAbove a)) hyy' _ _

  have V1_0 : ∀ c, m + 1 ≤ c → V1 c = 0 := by
    intro c hc; simp only [V1]; rw [dif_neg (by omega), if_neg (by omega)]
  have V1_cases : ∀ c, c < m + 1 → (c = i.val ∧ V1 c = ViF m i Vc) ∨
      (∃ b : Fin m, (i.succAbove b).val = c ∧ V1 c = Vc b) := by
    intro c hc
    by_cases hci : c = i.val
    · left; exact ⟨hci, by rw [hci, hV1i]⟩
    · right
      refine ⟨pidx m i c ⟨hc, hci⟩, succAbove_pidx m i c ⟨hc, hci⟩, ?_⟩
      simp only [V1]; rw [dif_pos ⟨hc, hci⟩]
  have V1_s : ∀ b, b < m + 1 → ∀ q : Fin (2 * (m + 1) + k + 1), m + 1 + k < q.val →
      V1 b q = if (NFOne.sg k (m + 1) q).val = b then 1 else 0 := by
    intro b hb q hq
    rcases V1_cases b hb with ⟨hbi, hv⟩ | ⟨b', hb', hv⟩
    · rw [hv, ViF_star m i Vc q hq, hbi]
    · rw [hv, hVs b' q hq, hb']
  have V1_iso : ∀ b c, b < m + 1 → c < m + 1 → herm (Hpk k (m + 1)) (V1 b) (V1 c) = 0 := by
    intro b c hb hc
    rcases V1_cases b hb with ⟨_, hv⟩ | ⟨b', _, hv⟩ <;> rcases V1_cases c hc with ⟨_, hw⟩ | ⟨c', _, hw⟩ <;> rw [hv, hw]
    · exact ViF_iso m i Vc
    · exact ViF_Vc m i Vc hVs c'
    · rw [herm_swap, ViF_Vc m i Vc hVs b', star_zero]
    · exact hVciso b' c'
  have V1_z : ∀ c, herm (Hpk k (m + 1)) z' (V1 c) = 0 := by
    intro c
    by_cases hc : c < m + 1
    · rcases V1_cases c hc with ⟨_, hv⟩ | ⟨b', _, hv⟩ <;> rw [hv]
      · exact hermitian_insertion_vector_orthogonal m i Vc z' hz
      · exact NFOne.herm_Hpk_of_inWb_eq_sum_wI k (m + 1) m (fun a => y (i.succAbove a)) z' (fun a => hzy _ (Fin.succAbove_ne i a)) _
    · rw [V1_0 c (by omega)]; simp [herm]
  have hn1 := one_add_projection_mem_isotropic_set (m + 1) z' hz V1 V1_0 V1_s V1_iso V1_z
  set n1 := 1 + NFOne.Pm k (m + 1) (m + 1) V1 with hn1def
  have hn1col : ∀ b : Fin (m + 1), n1 *ᵥ bvec (esI k (m + 1) b) = V1 b.val :=
    fun b => pm_col_star (m + 1) V1 V1_s b b.isLt

  have hU1 : IsUnit n1.det := WeylGroupFacts.isUnit_of_uh hn1.1
  set u := n1⁻¹ *ᵥ y i with hudef
  have hnu : n1 *ᵥ u = y i := by rw [hudef, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hU1, Matrix.one_mulVec]
  have hpres := herm_unitary n1 hn1.1
  have u_star : ∀ p : Fin (2 * (m + 1) + k + 1), m + 1 + k < p.val → u p = 0 := by
    intro p hp
    have hpv := p.isLt
    have hpe : p = esI k (m + 1) ⟨2 * (m + 1) + k - p.val, by omega⟩ := by ext; simp [esI]; omega
    have e := herm_bvec_eI (k := k) u (⟨2 * (m + 1) + k - p.val, by omega⟩ : Fin (m + 1))
    rw [hpe, ← e, ← hpres, hnu, hn1.2.1, herm_bvec_eI]
    exact hyi2 _ (by simp [esI]; omega)
  have u_X : ∀ c : Fin (m + 1), c ≠ i → u (eI k (m + 1) c) = 0 := by
    intro c hc
    have e := herm_bvec_esI (k := k) u c
    rw [← e, ← hpres, hnu, hn1col c]
    rcases V1_cases c.val c.isLt with ⟨hci, _⟩ | ⟨b', _, hv⟩
    · exact absurd (Fin.ext hci) hc
    · rw [hv]; exact NFOne.herm_Hpk_of_inWb_eq_sum_wI k (m + 1) m (fun a => y (i.succAbove a)) (y i) (fun a => hiso _ _) _
  set β := u (eI k (m + 1) i) with hβ
  set yb : Fin (2 * (m + 1) + k + 1) → ℂ := fun p => if m + 1 ≤ p.val ∧ p.val ≤ m + 1 + k then u p else 0 with hybdef
  have hyb : inWb k (m + 1) yb := by intro p hp; simp only [yb]; rw [if_neg (by omega)]
  have u_dec : u = fun p => yb p + β * bvec (eI k (m + 1) i) p := by
    funext p
    simp only [yb]
    by_cases hW : m + 1 ≤ p.val ∧ p.val ≤ m + 1 + k
    · have : p ≠ eI k (m + 1) i := by intro h; rw [h] at hW; simp [eI] at hW; omega
      simp [hW, bvec, Pi.single_apply, this]
    · rw [if_neg hW, zero_add]
      by_cases hX : p.val < m + 1
      · by_cases hpi : p.val = i.val
        · have : p = eI k (m + 1) i := by ext; simp [eI, hpi]
          rw [this]; simp [bvec, hβ]
        · have hpe : p = eI k (m + 1) ⟨p.val, hX⟩ := by ext; simp [eI]
          have hne : (⟨p.val, hX⟩ : Fin (m + 1)) ≠ i := by intro h; apply hpi; rw [← h]
          have hne2 : p ≠ eI k (m + 1) i := by intro h; apply hpi; rw [h]; simp [eI]
          rw [hpe, u_X _ hne]; simp [bvec, Pi.single_apply, ← hpe, hne2]
      · have hne2 : p ≠ eI k (m + 1) i := by intro h; apply hX; rw [h]; simp only [eI]; omega
        rw [u_star p (by omega)]; simp [bvec, Pi.single_apply, hne2]
  have tau_W : ∀ l : Fin (2 * (m + 1) + k + 1), m + 1 ≤ l.val ∧ l.val ≤ m + 1 + k → WeylGroupFacts.tau k (m + 1) l = l := by
    intro l hl; ext; rw [tau_val]; split_ifs <;> omega
  have tau_notW : ∀ l : Fin (2 * (m + 1) + k + 1), ¬ (m + 1 ≤ l.val ∧ l.val ≤ m + 1 + k) →
      (WeylGroupFacts.tau k (m + 1) l).val < m + 1 ∨ m + 1 + k < (WeylGroupFacts.tau k (m + 1) l).val := by
    intro l hl; rw [tau_val]; split_ifs <;> omega
  have yb_iso : herm (Hpk k (m + 1)) yb yb = 0 := by
    have : herm (Hpk k (m + 1)) yb yb = herm (Hpk k (m + 1)) u u := by
      rw [herm_expand, herm_expand]
      refine Finset.sum_congr rfl (fun l _ => ?_)
      by_cases hW : m + 1 ≤ l.val ∧ l.val ≤ m + 1 + k
      · rw [tau_W l hW]; simp only [yb, if_pos hW]
      · have h1 : yb l = 0 := by simp only [yb, if_neg hW]
        rw [h1]
        by_cases hX : l.val < m + 1
        · rw [u_star (WeylGroupFacts.tau k (m + 1) l) (by rw [tau_val]; split_ifs <;> omega)]; simp
        · rw [u_star l (by omega)]; simp
    rw [this, ← hpres, hnu, hiso]
  have yb_z : herm (Hpk k (m + 1)) z' yb = t := by
    have : herm (Hpk k (m + 1)) z' yb = herm (Hpk k (m + 1)) z' u := by
      rw [herm_expand, herm_expand]
      refine Finset.sum_congr rfl (fun l _ => ?_)
      by_cases hW : m + 1 ≤ l.val ∧ l.val ≤ m + 1 + k
      · simp only [yb, if_pos hW]
      · rw [hz (WeylGroupFacts.tau k (m + 1) l) (tau_notW l hW)]; simp
    rw [this, ← hpres, hnu, hn1.2.2.1, hzyi]

  set Z := herm (Hpk k (m + 1)) z' z' with hZdef
  set c2 : ℂ := star (β / star t) with hc2
  set c1 : ℂ := star (-(β / star t) * Z / t) with hc1
  set ν : Fin (2 * (m + 1) + k + 1) → ℂ := c1 • yb + c2 • z' with hνdef
  have hst : star t ≠ 0 := star_ne_zero.mpr ht
  have hν : inWb k (m + 1) ν := by
    intro p hp; simp only [ν, Pi.add_apply, Pi.smul_apply, hyb p hp, hz p hp, smul_zero, add_zero]
  have hzν : herm (Hpk k (m + 1)) z' ν = 0 := by
    rw [hνdef, herm_add_smul_right, yb_z, hc1, hc2, star_star, star_star]
    field_simp
    ring
  have hybν : herm (Hpk k (m + 1)) yb ν = β := by
    rw [hνdef, herm_add_smul_right, yb_iso, herm_swap k (m + 1) yb z', yb_z]
    simp only [hc2, star_star, mul_zero, zero_add]
    field_simp

  set V2 : ℕ → Fin (2 * (m + 1) + k + 1) → ℂ := fun c =>
    if hc : c < m + 1 then (if c = i.val then VpF m i ν else bvec (esI k (m + 1) ⟨c, hc⟩)) else 0 with hV2def
  have V2_cases : ∀ c (hc : c < m + 1), (c = i.val ∧ V2 c = VpF m i ν) ∨
      (c ≠ i.val ∧ V2 c = bvec (esI k (m + 1) ⟨c, hc⟩)) := by
    intro c hc
    by_cases hci : c = i.val
    · left; refine ⟨hci, ?_⟩; simp only [V2]; rw [dif_pos hc, if_pos hci]
    · right; refine ⟨hci, ?_⟩; simp only [V2]; rw [dif_pos hc, if_neg hci]
  have V2_0 : ∀ c, m + 1 ≤ c → V2 c = 0 := by intro c hc; simp only [V2]; rw [dif_neg (by omega)]
  have V2_s : ∀ b, b < m + 1 → ∀ q : Fin (2 * (m + 1) + k + 1), m + 1 + k < q.val →
      V2 b q = if (NFOne.sg k (m + 1) q).val = b then 1 else 0 := by
    intro b hb q hq
    rcases V2_cases b hb with ⟨hbi, hv⟩ | ⟨_, hv⟩
    · rw [hv, VpF_star m i ν hν q hq, hbi]
    · rw [hv, bvec_esI_star]
  have V2_iso : ∀ b c, b < m + 1 → c < m + 1 → herm (Hpk k (m + 1)) (V2 b) (V2 c) = 0 := by
    intro b c hb hc
    rcases V2_cases b hb with ⟨hbi, hv⟩ | ⟨hbi, hv⟩ <;> rcases V2_cases c hc with ⟨hci, hw⟩ | ⟨hci, hw⟩ <;> rw [hv, hw]
    · exact VpF_iso m i ν hν
    · exact VpF_esI m i ν hν _ (by intro h; apply hci; rw [← h])
    · rw [herm_swap, VpF_esI m i ν hν _ (by intro h; apply hbi; rw [← h]), star_zero]
    · exact bvec_esI_iso m _ _
  have V2_z : ∀ c, herm (Hpk k (m + 1)) z' (V2 c) = 0 := by
    intro c
    by_cases hc : c < m + 1
    · rcases V2_cases c hc with ⟨_, hv⟩ | ⟨_, hv⟩ <;> rw [hv]
      · exact hermitian_perturbed_vector_orthogonal m i ν z' hz hν hzν
      · rw [herm_bvec_esI]; exact hz _ (Or.inl (by simp only [eI]; omega))
    · rw [V2_0 c (by omega)]; simp [herm]
  have hn2 := one_add_projection_mem_isotropic_set (m + 1) z' hz V2 V2_0 V2_s V2_iso V2_z
  set n2 := 1 + NFOne.Pm k (m + 1) (m + 1) V2 with hn2def
  have hn2col : ∀ b : Fin (m + 1), n2 *ᵥ bvec (esI k (m + 1) b) = V2 b.val :=
    fun b => pm_col_star (m + 1) V2 V2_s b b.isLt

  have hn2yb : n2 *ᵥ yb = u := by
    rw [u_dec, hn2def, Matrix.add_mulVec, Matrix.one_mulVec]
    funext p
    rw [Pi.add_apply]
    congr 1
    simp only [Matrix.mulVec, dotProduct]
    by_cases hp : p.val < m + 1
    · have hterm : ∀ q, NFOne.Pm k (m + 1) (m + 1) V2 p q * yb q =
          if p.val = i.val then star (ν q) * (WeylGroupFacts.sgn k (m + 1) q * yb (WeylGroupFacts.tau k (m + 1) q)) else 0 := by
        intro q
        by_cases hW : m + 1 ≤ q.val ∧ q.val ≤ m + 1 + k
        · rw [NFOne.P_XW k (m + 1) (m + 1) V2 p q hp hW.1 hW.2, tau_W q hW]
          have hdW : NFOne.dW k (m + 1) q = WeylGroupFacts.sgn k (m + 1) q := rfl
          rcases V2_cases p.val hp with ⟨hpi, hv⟩ | ⟨hpi, hv⟩
          · rw [hv, if_pos hpi]
            unfold VpF
            have h1 : q ≠ esI k (m + 1) i := by intro h; rw [h] at hW; simp [esI] at hW; omega
            have h2 : q ≠ eI k (m + 1) i := by intro h; rw [h] at hW; simp [eI] at hW; omega
            simp only [bvec, Pi.single_apply, if_neg h1, if_neg h2, hdW]
            simp; ring
          · rw [hv, if_neg hpi]
            have h1 : q ≠ esI k (m + 1) ⟨p.val, hp⟩ := by intro h; rw [h] at hW; simp [esI] at hW; omega
            simp [bvec, Pi.single_apply, h1]
        · have h0 : yb q = 0 := hyb q (by omega)
          rw [h0, mul_zero]
          split_ifs
          · rw [hyb (WeylGroupFacts.tau k (m + 1) q) (tau_notW q hW)]; simp
          · rfl
      rw [Finset.sum_congr rfl (fun q _ => hterm q)]
      by_cases hpi : p.val = i.val
      · simp only [if_pos hpi]
        rw [← herm_expand, hybν]
        have : p = eI k (m + 1) i := by ext; simp [eI, hpi]
        simp [bvec, this]
      · have : p ≠ eI k (m + 1) i := by intro h; apply hpi; rw [h]; simp [eI]
        simp [hpi, bvec, Pi.single_apply, this]
    · have : p ≠ eI k (m + 1) i := by intro h; apply hp; rw [h]; simp only [eI]; omega
      rw [Finset.sum_eq_zero]
      · simp [bvec, Pi.single_apply, this]
      · intro q _
        by_cases hW : m + 1 ≤ q.val ∧ q.val ≤ m + 1 + k
        · rw [NFOne.P_rowWS_colW k (m + 1) (m + 1) V2 p q (by omega) hW.2, zero_mul]
        · rw [hyb q (by omega), mul_zero]

  set ystar : Fin (m + 1) → Fin (2 * (m + 1) + k + 1) → ℂ := fun a p => if m + 1 + k < p.val then y a p else 0 with hystar
  have hdec : ∀ a'' : Fin m, ystar (i.succAbove a'') =
      ∑ b : Fin m, Y' a'' b • bvec (esI k (m + 1) (i.succAbove b)) := by
    intro a''
    funext p
    simp only [ystar, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, bvec, Pi.single_apply]
    by_cases hp : m + 1 + k < p.val
    · rw [if_pos hp]
      have hpv := p.isLt
      by_cases hpi : (NFOne.sg k (m + 1) p).val = i.val
      · have hpe : p = esI k (m + 1) i := by ext; rw [sg_val'] at hpi; simp [esI]; omega
        rw [hpe, hyi _ (Fin.succAbove_ne i a'')]
        symm; apply Finset.sum_eq_zero; intro b _
        rw [if_neg, mul_zero]
        intro h; have := congrArg Fin.val h; simp [esI] at this
        exact hsne b (by have := (i.succAbove b).isLt; omega)
      · have hc : (NFOne.sg k (m + 1) p).val < m + 1 ∧ (NFOne.sg k (m + 1) p).val ≠ i.val := ⟨by rw [sg_val']; omega, hpi⟩
        have hsb := succAbove_pidx m i _ hc
        have hsv : (NFOne.sg k (m + 1) p).val = 2 * (m + 1) + k - p.val := sg_val' m p
        have hpe : p = esI k (m + 1) (i.succAbove (pidx m i _ hc)) := by
          ext; show p.val = 2 * (m + 1) + k - (i.succAbove (pidx m i _ hc)).val; rw [hsb, hsv]; omega
        rw [Finset.sum_eq_single (pidx m i _ hc)]
        · rw [if_pos hpe, mul_one]; exact congrArg (y (i.succAbove a'')) hpe
        · intro b _ hb
          rw [if_neg, mul_zero]
          intro h; apply hb
          rw [hpe] at h
          have hv := congrArg Fin.val h
          simp only [esI] at hv
          have h2 : i.succAbove (pidx m i _ hc) = i.succAbove b := by
            ext; have h3 := (i.succAbove b).isLt; have h4 := (i.succAbove (pidx m i _ hc)).isLt; omega
          exact (Fin.succAbove_right_injective h2).symm
        · simp
    · rw [if_neg hp]
      symm; apply Finset.sum_eq_zero; intro b _
      rw [if_neg, mul_zero]
      intro h; apply hp; rw [h]; simp [esI]; have := (i.succAbove b).isLt; omega
  have hn1y : ∀ a'' : Fin m, n1 *ᵥ ystar (i.succAbove a'') = y (i.succAbove a'') := by
    intro a''
    rw [hdec, Matrix.mulVec_sum]
    simp only [Matrix.mulVec_smul, hn1col, hV1c, Vc, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    simp only [← Finset.sum_smul]
    rw [Finset.sum_eq_single a'']
    · have := congrFun (congrFun hYN a'') a''
      rw [Matrix.mul_apply, Matrix.one_apply, if_pos rfl] at this
      rw [this, one_smul]
    · intro a' _ ha'
      have := congrFun (congrFun hYN a'') a'
      rw [Matrix.mul_apply, Matrix.one_apply, if_neg (Ne.symm ha')] at this
      rw [this, zero_smul]
    · simp
  have hn2y : ∀ a'' : Fin m, n2 *ᵥ ystar (i.succAbove a'') = ystar (i.succAbove a'') := by
    intro a''
    rw [hdec, Matrix.mulVec_sum]
    simp only [Matrix.mulVec_smul, hn2col]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rcases V2_cases (i.succAbove b).val (i.succAbove b).isLt with ⟨hbi, _⟩ | ⟨_, hv⟩
    · exact absurd hbi (hsne b)
    · rw [hv]
  refine ⟨n1 * n2, mul_mem_isotropic_unipotent_set z' (m + 1) (m + 1) V1 V2 hn1 hn2, fun a => if a = i then yb else ystar a, fun a => ?_⟩
  by_cases ha : a = i
  · subst ha
    simp only [if_true]
    refine ⟨by rw [← Matrix.mulVec_mulVec, hn2yb, hnu], fun h => absurd rfl h, fun _ => ⟨hyb, yb_z⟩⟩
  · simp only [if_neg ha]
    obtain ⟨a'', rfl⟩ := Fin.exists_succAbove_eq ha
    refine ⟨by rw [← Matrix.mulVec_mulVec, hn2y, hn1y], fun _ => ⟨?_, ?_⟩, fun h => absurd h ha⟩
    · intro p hp; simp only [ystar]; rw [if_neg (by omega)]
    · intro p hp; simp only [ystar]; rw [if_pos hp]

end

end Formalism.FourierDecayAlt.P.SignAntidiagonal
