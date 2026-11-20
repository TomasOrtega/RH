import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.DualForm
open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

set_option autoImplicit false

namespace UpperTheory.Gal.productCup_of_system

/- English proof (translation)
Simplify using `[acx, Submodule.mem_pi]`.
-/
private lemma mem_acx_C {ι E : Type} [LinearOrder ι] [AddCommGroup E] [Module ℂ E]
    (A : Finset ι → Submodule ℂ E) (w : ι → Module.End ℂ E) (n : ℤ) (c : Finset ι → E) :
    c ∈ (acx A w).C n ↔ ∀ s, c s ∈ (if (s.card : ℤ) = n then A s else ⊥) := by
  simp [acx, Submodule.mem_pi]

/- English proof (translation)
Simplify using `[wd, map_sum, h, map_zsmul]`.
-/
private lemma wd_map {ι E E' : Type} [LinearOrder ι] [AddCommGroup E] [Module ℂ E] [AddCommGroup E'] [Module ℂ E']
    (w : ι → Module.End ℂ E) (w' : ι → Module.End ℂ E') (φ : E →ₗ[ℂ] E')
    (h : ∀ i y, φ (w i y) = w' i (φ y)) (c : Finset ι → E) (t : Finset ι) :
    wd w' (fun s => φ (c s)) t = φ (wd w c t) := by
  simp [wd, map_sum, h, map_zsmul]

/- English proof (translation)
Establish `h1` using `(hM d S E T).1`. Establish `h2` using `(hM d S E T).2.1`. Use function extensionality and compare the values at `L`. Establish `h3` using `congrFun h1 (uni {i} L)`. Rewrite `h3` using `[(hU (Fin (d + 1)) (Mi d) S _ (detC T.rowMu) {i} L).1]`.

Establish `h5 : wd (fun a => (Algebra.lmul ℂ S) (app (fun _ => 1) T.mu (inlE a))) (fun b' => detC T.rowMu (uni b' L)) {i} = 0`. Simplify using `[wd, h2]`. Rewrite `h3` using `[h5, zero_add]`. Establish `h4 : wd (fun l => Algebra.lmul ℂ S (T.mu l)) (fun L' => detC T.rowMu (uni {i} L')) L = 0`. Establish `h6 : ((-1 : ℤ) ^ ({i} : Finset (Fin (d + 1))).card) • wd (fun l => Algebra.lmul ℂ S (T.mu l)) (fun L' => detC T.rowMu (uni {i} L')) L = 0` using `h3`.

Simplify using `using h6`. Set `φ : S →ₗ[ℂ] E` to `{ toFun := fun y => T.act (y * g) m map_add' := fun a b => by simp [add_mul] map_smul' := fun c a => by simp }`. Establish `h7` using `wd_map (fun l => Algebra.lmul ℂ S (T.mu l)) (fun l => T.act (T.mu l)) φ (fun l y => by show T.act (T.mu l * y * g) m = T.act (T.mu l) (T.act (y * g) m)`. Rewrite using `[mul_assoc, map_mul, Module.End.mul_apply]) (fun L' => detC T.rowMu (uni {i} L')) L`. Rewrite `h7` using `[h4, map_zero]`.

Conclude with `h7`.
-/
private lemma minors_cocycle (hU : WdUni) (hM : ThMu) {d : ℕ} {S E : Type} [CommRing S] [Algebra ℂ S]
    [AddCommGroup E] [Module ℂ E] (T : Sys d S E) (i : Fin (d + 1)) (g : S) (m : E) :
    wd (fun l => T.act (T.mu l)) (fun L => T.act (detC T.rowMu (uni {i} L) * g) m) = 0 := by
  have h1 := (hM d S E T).1
  have h2 := (hM d S E T).2.1
  funext L
  have h3 := congrFun h1 (uni {i} L)
  rw [(hU (Fin (d + 1)) (Mi d) S _ (detC T.rowMu) {i} L).1] at h3
  have h5 : wd (fun a => (Algebra.lmul ℂ S) (app (fun _ => 1) T.mu (inlE a)))
      (fun b' => detC T.rowMu (uni b' L)) {i} = 0 := by
    simp [wd, h2]
  rw [h5, zero_add] at h3
  have h4 : wd (fun l => Algebra.lmul ℂ S (T.mu l)) (fun L' => detC T.rowMu (uni {i} L')) L = 0 := by
    have h6 : ((-1 : ℤ) ^ ({i} : Finset (Fin (d + 1))).card) •
        wd (fun l => Algebra.lmul ℂ S (T.mu l)) (fun L' => detC T.rowMu (uni {i} L')) L = 0 := h3
    simpa using h6
  let φ : S →ₗ[ℂ] E :=
    { toFun := fun y => T.act (y * g) m
      map_add' := fun a b => by simp [add_mul]
      map_smul' := fun c a => by simp }
  have h7 := wd_map (fun l => Algebra.lmul ℂ S (T.mu l)) (fun l => T.act (T.mu l)) φ
    (fun l y => by
      show T.act (T.mu l * y * g) m = T.act (T.mu l) (T.act (y * g) m)
      rw [mul_assoc, map_mul, Module.End.mul_apply]) (fun L' => detC T.rowMu (uni {i} L')) L
  rw [h4, map_zero] at h7
  exact h7

/- English proof (translation)
Establish `hpi : pk ({i} : Finset (Fin (d + 1))) = i` using `by simp [pk]`. Establish `hpj : pk ({j} : Finset (Fin (d + 1))) = j` using `by simp [pk]`. Establish `hStab` using `hG.stab {i} {j} ⟨i, by simp⟩ ⟨j, by simp⟩`. Take `⟨hAdmMu, hLat⟩` from `hML d S E T hG`. Set `r : Mi d ⊕ₗ κ → S` to `T.r (app n11 n) (app T.mu z) i j`.

Set `rm : Mi d → S` to `T.r n11 T.mu i j`. Set `u : Mi d ⊕ₗ κ → Sˣ` to `T.u (app n11 n) i j`. Set `um : Mi d → Sˣ` to `T.u n11 i j`. Establish `hrm : ∀ l, rm l ∈ T.R {i} {j}` using `hAdmMu i j`. Establish `hr : ∀ l, r l ∈ T.R {i} {j}`.

Introduce `l`. Take `⟨l, rfl⟩` from `toLex.surjective l`. Break down `l with l | l` into its components or cases. Conclude with `hAdmMu i j l`. Conclude with `hAdm i j l`.

Take `⟨P, hPdef⟩ : ∃ P : Sˣ, P = ∏ a ∈ ({i} : Finset (Fin (d + 1)))ᶜ, T.X a` from `⟨_, rfl⟩`. Rewrite `hv` using `[← hPdef]`. Set `g : S` to `(-1) ^ d * ((T.X i : S) ^ d * ((P⁻¹ : Sˣ) : S))`. Set `c1 : Finset (Mi d) → E` to `fun L => T.act (detC T.rowMu (uni {i} L) * g) m`. Establish `hc1 : c1 ∈ (kosT T.act (T.M {i} {j}) um T.mu).Z d`.

Use `⟨(mem_acx_C _ _ _ _).2 fun L => ?_, LinearMap.mem_ker.2 (minors_cocycle hU hM T i g m)⟩` and prove the remaining obligations. Distinguish the cases in `hL : (L.card : ℤ) = d`. Establish `hL' : L.card = d` using `by exact_mod_cast hL`. Rewrite using `[if_pos hL]`. Take `⟨s, hs, hdet⟩` from `hLat {i} {j} L ⟨i, by simp⟩ j (by simp)`.

Use `⟨T.act ((-1) ^ d * s) m, hStab _ ((T.R {i} {j}).mul_mem ((T.R {i} {j}).pow_mem ((T.R {i} {j}).neg_mem ((T.R {i} {j}).one_mem)) d) hs) _ hmM, ?_⟩` and prove the remaining obligations. Establish `hPP : (P : S) * ((P⁻¹ : Sˣ) : S) = 1` using `Units.mul_inv P`. Establish `hPc : ∏ a ∈ ({i} : Finset (Fin (d + 1)))ᶜ, (T.X a : S) = P`. Rewrite using `[hPdef, Units.coe_prod]`. Establish `hum : ((∏ l ∈ L, um l : Sˣ) : S) = ((T.X i : S) * T.Y j) ^ d`.

Simplify using `[um, Sys.u, n11, Finset.prod_const, hL']`. Use `show T.act _ (T.act _ m) = T.act (detC T.rowMu (uni {i} L) * g) m`. Rewrite using `[← Module.End.mul_apply, ← map_mul, hum, hdet, hPc, hL']`. Use `congr 2`. Simplify using `only [g]`.

Rewrite using `[mul_pow]`. Take the linear combination `(-(s * (T.Y j : S) ^ d * (-1) ^ d * (T.X i : S) ^ d)) * hPP`. Rewrite using `[if_neg hL]`. Establish `hcard : (uni {i} L).card ≠ d + 1`. Introduce `h`.

Apply `hL` to reduce the goal to its premises. Establish `: (uni ({i} : Finset (Fin (d + 1))) L).card = 1 + L.card` using `by simp [uni]`. Use linear arithmetic over natural numbers and integers. Establish `: detC T.rowMu (uni {i} L) = 0` using `dif_neg hcard`. Simplify using `[c1, this]`.

Establish `hc1'` using `((hRS S E T.act (Mi d) (T.M {i} {j}) um rm T.mu (fun _ => rfl) d c1).2.1).1 hc1`. Set `m0 : E` to `unsc T.act um c1 (img (dj j))`. Establish `hm0M : m0 ∈ T.M {i} {j}`. Establish `h` using `(mem_acx_C _ _ _ _).1 hc1'.1 (img (dj j))`. Rewrite `h` using `[if_pos (by simp [img])]`.

Conclude with `h`. Establish `hAc1 : ∀ L, Ac (c1 L) (π (detC T.rowMu (uni {i} L) * g) * v)` using `fun L => hmul _ _ _ hm`. Establish `hπ0 : ∀ l, π (r l) = 0`. Introduce `l`. Take `⟨l, rfl⟩` from `toLex.surjective l`.

Break down `l with l | l` into its components or cases. Use `show π (T.mu l * _) = 0`. Rewrite using `[map_mul, hmu, zero_mul]`. Use `show π (z l * _) = 0`. Rewrite using `[map_mul, hz, zero_mul]`.

Establish `hkill : ∀ l, T.act (r l) m0 ∈ sm T.act (T.M {i} {j}) (Set.range fun a => r (((dj j).trans (inlE : Mi d ↪o Mi d ⊕ₗ κ)) a))`. Introduce `l`. Establish `h0 : Ac (T.act (r l) m0) 0`. Establish `h` using `hmul _ _ (r l) (hmul _ _ (((∏ l ∈ img (dj j), um l)⁻¹ : Sˣ) : S) (hAc1 (img (dj j))))`. Rewrite `h` using `[hπ0 l, zero_mul]`.

Conclude with `h`. Conclude with `hcol _ (hStab _ (hr l) _ hm0M) h0`. Take `⟨C, hC, hCe⟩` from `hK2E S E T.act (Mi d ⊕ₗ κ) (T.R {i} {j}) (T.M {i} {j}) r d ((dj j).trans (inlE : Mi d ↪o Mi d ⊕ₗ κ)) hStab hr hKE m0 hm0M hkill`. Set `C' : Finset (Mi d) → E` to `fun L => C (L.map inlE.toEmbedding)`. Establish `hC' : C' ∈ (kos T.act (T.M {i} {j}) rm).Z d`.

Use `⟨(mem_acx_C _ _ _ _).2 fun L => ?_, LinearMap.mem_ker.2 ?_⟩` and prove the remaining obligations. Establish `h` using `(mem_acx_C _ _ _ _).1 hC.1 (L.map inlE.toEmbedding)`. Rewrite `h` using `[Finset.card_map]`. Conclude with `h`. Establish `hker : wd (fun l => T.act (r l)) C = 0` using `LinearMap.mem_ker.1 hC.2`.

Use function extensionality and compare the values at `s`. Conclude with `((hB (Mi d ⊕ₗ κ) E (fun _ => ⊤) (fun l => T.act (r l))).2.2.2.2.2 (Mi d) inlE C s).trans (congrFun hker _)`. Establish `hD : C' - unsc T.act um c1 ∈ (kos T.act (T.M {i} {j}) rm).Z d` using `sub_mem hC' hc1'`. Establish `hD0 : (C' - unsc T.act um c1) (img (dj j)) = 0`. Establish `himg : (img (dj j)).map inlE.toEmbedding = img ((dj j).trans (inlE : Mi d ↪o Mi d ⊕ₗ κ))`.

Simplify using `only [img, Finset.map_map]`. Both sides reduce to the same expression. Use `show C _ - m0 = 0`. Rewrite using `[himg, hCe, sub_self]`. Establish `hDB` using `hK2I S E T.act (Mi d) (T.R {i} {j}) (T.M {i} {j}) rm d (dj j) hStab hrm hKE _ hD (by rw [hD0]; exact zero_mem _)`.

Establish `hDs` using `(hKS S E T.act (Mi d) (T.R {i} {j}) (T.M {i} {j}) rm hStab hrm).2 d _ hDB`. Use `⟨unsc T.act u⁻¹ C, ?_, ?_⟩` and prove the remaining obligations. Unfold `Sys.colCx`. Rewrite using `[hpi, hpj]`. Establish `h` using `hRS S E T.act (Mi d ⊕ₗ κ) (T.M {i} {j}) u r (app T.mu z) (fun _ => rfl) d (unsc T.act u⁻¹ C)`.

Establish `h'` using `hRS S E T.act (Mi d ⊕ₗ κ) (T.M {i} {j}) u r (app T.mu z) (fun _ => rfl) d C`. Conclude with `h.2.1.2 (by rw [h'.2.2.2.2]; exact hC)`. Introduce `L hL`. Establish `hmap : uni L (∅ : Finset κ) = L.map inlE.toEmbedding`. Use extensionality with `t`.

Take `⟨t, rfl⟩` from `toLex.surjective t`. Apply the tactic sequence `rcases t with t | t <;> simp [uni, inlE]`. Establish `hprod : ((∏ l ∈ L.map inlE.toEmbedding, u⁻¹ l)⁻¹ : Sˣ) = ∏ l ∈ L, um l`. Rewrite using `[Finset.prod_map]`. Simplify using `only [Pi.inv_apply, Finset.prod_inv_distrib, inv_inv]`.

Both sides reduce to the same expression. Establish `hval : unsc T.act u⁻¹ C (uni L ∅) = T.act ((∏ l ∈ L, um l : Sˣ) : S) ((C' - unsc T.act um c1) L) + c1 L` using `by show T.act _ (C _) = _`. Rewrite using `[hmap, hprod, Pi.sub_apply, map_sub]`. Use `show _ = _ - T.act _ (T.act _ (c1 L)) + c1 L`. Rewrite using `[← Module.End.mul_apply, ← map_mul, Units.mul_inv, map_one, Module.End.one_apply, sub_add_cancel]`.

Rewrite using `[hval]`. Establish `hfin : π (detC T.rowMu (uni {i} L) * g) * v = (-1) ^ d * π (detC T.rowMu (uni {i} L))`. Establish `hg : π g = (-1) ^ d * π ((T.X i : S) ^ d * ((P⁻¹ : Sˣ) : S))`. Simplify using `only [g]`. Rewrite using `[map_mul, map_pow, map_neg, map_one]`.

Rewrite using `[map_mul, hg]`. Take the linear combination `((-1) ^ d * π (detC T.rowMu (uni {i} L))) * hv`. Establish `h` using `hadd _ _ _ _ (hsm (∏ l ∈ L, um l) _ (hDs L)) (hAc1 L)`. Rewrite `h` using `[zero_add, hfin]`. Conclude with `h`.
-/
private lemma core (hK2E : KoszulCocycleExistsWithPrescribedComponent) (hK2I : KoszulBoundaryOfComponentMemIdeal) (hKS : KSub) (hRS : RS) (hM : ThMu) (hML : ThMuLat)
    (hB : WdBasic) (hU : WdUni) {d : ℕ} {S E A : Type} [CommRing S] [Algebra ℂ S] [AddCommGroup E] [Module ℂ E]
    [CommRing A] (T : Sys d S E) (hG : T.Good) {κ : Type} [LinearOrder κ] [Fintype κ] (n : κ → ℕ × ℕ)
    (z : κ → S) (hAdm : T.admitted n z) (π : S →+* A) (Ac : E → A → Prop)
    (hadd : ∀ m m' c c', Ac m c → Ac m' c' → Ac (m + m') (c + c'))
    (hmul : ∀ m c s, Ac m c → Ac (T.act s m) (π s * c))
    (i j : Fin (d + 1))
    (hsm : ∀ (w : Sˣ) m, m ∈ sm T.act (T.M {i} {j}) (Set.range (T.r n11 T.mu i j)) → Ac (T.act w m) 0)
    (hKE : KE (kos T.act (T.M {i} {j}) fun l => T.r n11 T.mu i j (dj j l)) d)
    (hcol : ∀ m ∈ T.M {i} {j}, Ac m 0 →
      m ∈ sm T.act (T.M {i} {j}) (Set.range fun l => T.r n11 T.mu i j (dj j l)))
    (hz : ∀ l, π (z l) = 0) (hmu : ∀ l, π (T.mu l) = 0)
    (m : E) (hmM : m ∈ T.M {i} {j}) (v : A) (hm : Ac m v)
    (hv : π ((T.X i : S) ^ d * (((∏ a ∈ ({i} : Finset (Fin (d + 1)))ᶜ, T.X a)⁻¹ : Sˣ) : S)) * v = 1) :
    ∃ c ∈ (T.colCx (app n11 n) (app T.mu z) {i} {j}).Z d, ∀ L : Finset (Mi d), L.card = d →
      Ac (c (uni L ∅)) ((-1) ^ d * π (detC T.rowMu (uni {i} L))) := by
  have hpi : pk ({i} : Finset (Fin (d + 1))) = i := by simp [pk]
  have hpj : pk ({j} : Finset (Fin (d + 1))) = j := by simp [pk]
  have hStab := hG.stab {i} {j} ⟨i, by simp⟩ ⟨j, by simp⟩
  obtain ⟨hAdmMu, hLat⟩ := hML d S E T hG
  let r : Mi d ⊕ₗ κ → S := T.r (app n11 n) (app T.mu z) i j
  let rm : Mi d → S := T.r n11 T.mu i j
  let u : Mi d ⊕ₗ κ → Sˣ := T.u (app n11 n) i j
  let um : Mi d → Sˣ := T.u n11 i j
  have hrm : ∀ l, rm l ∈ T.R {i} {j} := hAdmMu i j
  have hr : ∀ l, r l ∈ T.R {i} {j} := by
    intro l
    obtain ⟨l, rfl⟩ := toLex.surjective l
    rcases l with l | l
    · exact hAdmMu i j l
    · exact hAdm i j l
  obtain ⟨P, hPdef⟩ : ∃ P : Sˣ, P = ∏ a ∈ ({i} : Finset (Fin (d + 1)))ᶜ, T.X a := ⟨_, rfl⟩
  rw [← hPdef] at hv
  let g : S := (-1) ^ d * ((T.X i : S) ^ d * ((P⁻¹ : Sˣ) : S))
  let c1 : Finset (Mi d) → E := fun L => T.act (detC T.rowMu (uni {i} L) * g) m
  have hc1 : c1 ∈ (kosT T.act (T.M {i} {j}) um T.mu).Z d := by
    refine ⟨(mem_acx_C _ _ _ _).2 fun L => ?_, LinearMap.mem_ker.2 (minors_cocycle hU hM T i g m)⟩
    by_cases hL : (L.card : ℤ) = d
    · have hL' : L.card = d := by exact_mod_cast hL
      rw [if_pos hL]
      obtain ⟨s, hs, hdet⟩ := hLat {i} {j} L ⟨i, by simp⟩ j (by simp)
      refine ⟨T.act ((-1) ^ d * s) m, hStab _ ((T.R {i} {j}).mul_mem
        ((T.R {i} {j}).pow_mem ((T.R {i} {j}).neg_mem ((T.R {i} {j}).one_mem)) d) hs) _ hmM, ?_⟩
      have hPP : (P : S) * ((P⁻¹ : Sˣ) : S) = 1 := Units.mul_inv P
      have hPc : ∏ a ∈ ({i} : Finset (Fin (d + 1)))ᶜ, (T.X a : S) = P := by
        rw [hPdef, Units.coe_prod]
      have hum : ((∏ l ∈ L, um l : Sˣ) : S) = ((T.X i : S) * T.Y j) ^ d := by
        simp [um, Sys.u, n11, Finset.prod_const, hL']
      show T.act _ (T.act _ m) = T.act (detC T.rowMu (uni {i} L) * g) m
      rw [← Module.End.mul_apply, ← map_mul, hum, hdet, hPc, hL']
      congr 2
      simp only [g]
      rw [mul_pow]
      linear_combination (-(s * (T.Y j : S) ^ d * (-1) ^ d * (T.X i : S) ^ d)) * hPP
    · rw [if_neg hL]
      have hcard : (uni {i} L).card ≠ d + 1 := by
        intro h
        apply hL
        have : (uni ({i} : Finset (Fin (d + 1))) L).card = 1 + L.card := by simp [uni]
        omega
      have : detC T.rowMu (uni {i} L) = 0 := dif_neg hcard
      simp [c1, this]
  have hc1' := ((hRS S E T.act (Mi d) (T.M {i} {j}) um rm T.mu (fun _ => rfl) d c1).2.1).1 hc1
  let m0 : E := unsc T.act um c1 (img (dj j))
  have hm0M : m0 ∈ T.M {i} {j} := by
    have h := (mem_acx_C _ _ _ _).1 hc1'.1 (img (dj j))
    rw [if_pos (by simp [img])] at h
    exact h
  have hAc1 : ∀ L, Ac (c1 L) (π (detC T.rowMu (uni {i} L) * g) * v) := fun L => hmul _ _ _ hm
  have hπ0 : ∀ l, π (r l) = 0 := by
    intro l
    obtain ⟨l, rfl⟩ := toLex.surjective l
    rcases l with l | l
    · show π (T.mu l * _) = 0
      rw [map_mul, hmu, zero_mul]
    · show π (z l * _) = 0
      rw [map_mul, hz, zero_mul]
  have hkill : ∀ l, T.act (r l) m0 ∈ sm T.act (T.M {i} {j})
      (Set.range fun a => r (((dj j).trans (inlE : Mi d ↪o Mi d ⊕ₗ κ)) a)) := by
    intro l
    have h0 : Ac (T.act (r l) m0) 0 := by
      have h := hmul _ _ (r l) (hmul _ _ (((∏ l ∈ img (dj j), um l)⁻¹ : Sˣ) : S) (hAc1 (img (dj j))))
      rw [hπ0 l, zero_mul] at h
      exact h
    exact hcol _ (hStab _ (hr l) _ hm0M) h0
  obtain ⟨C, hC, hCe⟩ := hK2E S E T.act (Mi d ⊕ₗ κ) (T.R {i} {j}) (T.M {i} {j}) r d ((dj j).trans (inlE : Mi d ↪o Mi d ⊕ₗ κ))
    hStab hr hKE m0 hm0M hkill
  let C' : Finset (Mi d) → E := fun L => C (L.map inlE.toEmbedding)
  have hC' : C' ∈ (kos T.act (T.M {i} {j}) rm).Z d := by
    refine ⟨(mem_acx_C _ _ _ _).2 fun L => ?_, LinearMap.mem_ker.2 ?_⟩
    · have h := (mem_acx_C _ _ _ _).1 hC.1 (L.map inlE.toEmbedding)
      rw [Finset.card_map] at h
      exact h
    · have hker : wd (fun l => T.act (r l)) C = 0 := LinearMap.mem_ker.1 hC.2
      funext s
      exact ((hB (Mi d ⊕ₗ κ) E (fun _ => ⊤) (fun l => T.act (r l))).2.2.2.2.2 (Mi d) inlE C s).trans
        (congrFun hker _)
  have hD : C' - unsc T.act um c1 ∈ (kos T.act (T.M {i} {j}) rm).Z d := sub_mem hC' hc1'
  have hD0 : (C' - unsc T.act um c1) (img (dj j)) = 0 := by
    have himg : (img (dj j)).map inlE.toEmbedding = img ((dj j).trans (inlE : Mi d ↪o Mi d ⊕ₗ κ)) := by
      simp only [img, Finset.map_map]
      rfl
    show C _ - m0 = 0
    rw [himg, hCe, sub_self]
  have hDB := hK2I S E T.act (Mi d) (T.R {i} {j}) (T.M {i} {j}) rm d (dj j) hStab hrm hKE _ hD
    (by rw [hD0]; exact zero_mem _)
  have hDs := (hKS S E T.act (Mi d) (T.R {i} {j}) (T.M {i} {j}) rm hStab hrm).2 d _ hDB
  refine ⟨unsc T.act u⁻¹ C, ?_, ?_⟩
  · unfold Sys.colCx
    rw [hpi, hpj]
    have h := hRS S E T.act (Mi d ⊕ₗ κ) (T.M {i} {j}) u r (app T.mu z) (fun _ => rfl) d
      (unsc T.act u⁻¹ C)
    have h' := hRS S E T.act (Mi d ⊕ₗ κ) (T.M {i} {j}) u r (app T.mu z) (fun _ => rfl) d C
    exact h.2.1.2 (by rw [h'.2.2.2.2]; exact hC)
  · intro L hL
    have hmap : uni L (∅ : Finset κ) = L.map inlE.toEmbedding := by
      ext t
      obtain ⟨t, rfl⟩ := toLex.surjective t
      rcases t with t | t <;> simp [uni, inlE]
    have hprod : ((∏ l ∈ L.map inlE.toEmbedding, u⁻¹ l)⁻¹ : Sˣ) = ∏ l ∈ L, um l := by
      rw [Finset.prod_map]
      simp only [Pi.inv_apply, Finset.prod_inv_distrib, inv_inv]
      rfl
    have hval : unsc T.act u⁻¹ C (uni L ∅) =
        T.act ((∏ l ∈ L, um l : Sˣ) : S) ((C' - unsc T.act um c1) L) + c1 L := by
      show T.act _ (C _) = _
      rw [hmap, hprod, Pi.sub_apply, map_sub]
      show _ = _ - T.act _ (T.act _ (c1 L)) + c1 L
      rw [← Module.End.mul_apply, ← map_mul, Units.mul_inv, map_one, Module.End.one_apply,
        sub_add_cancel]
    rw [hval]
    have hfin : π (detC T.rowMu (uni {i} L) * g) * v = (-1) ^ d * π (detC T.rowMu (uni {i} L)) := by
      have hg : π g = (-1) ^ d * π ((T.X i : S) ^ d * ((P⁻¹ : Sˣ) : S)) := by
        simp only [g]
        rw [map_mul, map_pow, map_neg, map_one]
      rw [map_mul, hg]
      linear_combination ((-1) ^ d * π (detC T.rowMu (uni {i} L))) * hv
    have h := hadd _ _ _ _ (hsm (∏ l ∈ L, um l) _ (hDs L)) (hAc1 L)
    rw [zero_add, hfin] at h
    exact h

end UpperTheory.Gal.productCup_of_system

/- English proof (translation)
Introduce `hId hCol hK2E hK2I hKS hRS hM hML _ hKap hAL _ hGood hB hU F K _ _ _ _ _ _ d x hc τ hτ a ha κ _ _ n z hz i j`. Take `⟨m, hmM, hm⟩` from `hId F K d x hc τ hτ a ha i j`. Take `⟨hAL1, hAL2, -, hAL4, -, -⟩` from `hAL F K d x hc τ hτ a`. Take `⟨hKE, hCZ⟩` from `hCol F K d x hc τ hτ a ha {i} {j} i (by simp) j (by simp)`. Establish `hG` using `(hGood F K d x hc a).1`.

Set `π : K ⊗[ℂ] K →ₐ[ℂ] K` to `Algebra.TensorProduct.lmul' ℂ`. Establish `hπX : ∀ b, π ((sysZ K x a).X b : K ⊗[ℂ] K) = algebraMap F K (x b)`. Introduce `b`. Simplify using `[π, sysZ]`. Establish `hπY : ∀ b, π ((sysZ K x a).Y b : K ⊗[ℂ] K) = algebraMap F K (x b)`.

Introduce `b`. Simplify using `[π, sysZ]`. Establish `hmu : ∀ l, π ((sysZ K x a).mu l) = 0`. Introduce `l`. Simplify using `only [Sys.mu, map_sub, map_mul, hπX, hπY]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hv : (π : K ⊗[ℂ] K →+* K) (((sysZ K x a).X i : K ⊗[ℂ] K) ^ d * (((∏ b ∈ ({i} : Finset (Fin (d + 1)))ᶜ, (sysZ K x a).X b)⁻¹ : (K ⊗[ℂ] K)ˣ) : K ⊗[ℂ] K)) * algebraMap F K (omG x i) = 1`. Take `⟨P, hPdef⟩ : ∃ P : (K ⊗[ℂ] K)ˣ, P = ∏ b ∈ ({i} : Finset (Fin (d + 1)))ᶜ, (sysZ K x a).X b` from `⟨_, rfl⟩`. Rewrite using `[← hPdef]`. Use `show π (((sysZ K x a).X i : K ⊗[ℂ] K) ^ d * ((P⁻¹ : (K ⊗[ℂ] K)ˣ) : K ⊗[ℂ] K)) * _ = 1`.

Establish `hP1 : π (P : K ⊗[ℂ] K) * π ((P⁻¹ : (K ⊗[ℂ] K)ˣ) : K ⊗[ℂ] K) = 1`. Rewrite using `[← map_mul, Units.mul_inv, map_one]`. Establish `hP2 : π (P : K ⊗[ℂ] K) = ∏ b ∈ ({i} : Finset (Fin (d + 1)))ᶜ, algebraMap F K (x b)`. Rewrite using `[hPdef, Units.coe_prod, map_prod]`. Conclude with `Finset.prod_congr rfl fun b _ => hπX b`.

Establish `hxi : algebraMap F K (x i) ≠ 0`. Simplify using the standard rewrite rules. Establish `hom : algebraMap F K (omG x i) = algebraMap F K (x i) * (∏ b ∈ ({i} : Finset (Fin (d + 1)))ᶜ, algebraMap F K (x b)) / algebraMap F K (x i) ^ (d + 1)`. Simplify using `only [omG, map_prod, map_div₀, Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]`. Rewrite using `[Fintype.prod_eq_mul_prod_compl i, map_pow]`.

Rewrite using `[hom, ← hP2, map_mul, map_pow, hπX]`. Establish `e1 : algebraMap F K (x i) * π (P : K ⊗[ℂ] K) / algebraMap F K (x i) ^ (d + 1) * algebraMap F K (x i) ^ d = π (P : K ⊗[ℂ] K)`. Rewrite using `[pow_succ]`. Clear the denominators using the available nonvanishing facts. Combine the equalities or inequalities in the displayed calculation.

Establish `hAdm : (sysZ K x a).admitted n z`. Establish `hX : (sysZ K x a).X = (sysZ K x 0).X` using `rfl`. Establish `hY : (sysZ K x a).Y = (sysZ K x 0).Y` using `rfl`. Establish `hR : (sysZ K x a).R = (sysZ K x 0).R` using `rfl`. Introduce `i' j' l`.

Establish `h` using `hz.adm i' j' l`. Simplify using `only [Sys.r, Sys.u] at h ⊢`. Rewrite using `[hX, hY, hR]`. Conclude with `h`. Take `⟨c, hc1, hc2⟩` from `core hK2E hK2I hKS hRS hM hML hB hU (sysZ K x a) hG n z hAdm (π : K ⊗[ℂ] K →+* K) (Acts (F := F) K τ a) (fun _ _ _ _ h h' => (hAL1 _ _ _ _ h h').1) (fun _ _ s h => hAL2 _ _ s h) i j (fun w _ h => hAL4 w _ _ i j h) hKE hCZ hz.diag hmu m hmM _ hm hv`.

Use `⟨c, hc1, fun L hL => ?_⟩` and prove the remaining obligations. Establish `hk` using `hKap F K d x hc _ _ (sysZ K x a) π hπX hπY i L hL`. Establish `h` using `hc2 L hL`. Rewrite `h` using `[show (π : K ⊗[ℂ] K →+* K) (detC (sysZ K x a).rowMu (uni {i} L)) = kap K x L from hk]`. Conclude with `h`.
-/
theorem UpperTheory.Gal.productCup_of_system.zCol_of :
    IdIJ → ColZ → KoszulCocycleExistsWithPrescribedComponent → KoszulBoundaryOfComponentMemIdeal → KSub → RS → ThMu → ThMuLat → MuSpan → KapInd → ActsLin → SysOk → GoodZ → WdBasic → WdUni → ZCol := by
  intro hId hCol hK2E hK2I hKS hRS hM hML _ hKap hAL _ hGood hB hU F K _ _ _ _ _ _ d x hc τ hτ a ha κ _ _ n z hz
    i j
  obtain ⟨m, hmM, hm⟩ := hId F K d x hc τ hτ a ha i j
  obtain ⟨hAL1, hAL2, -, hAL4, -, -⟩ := hAL F K d x hc τ hτ a
  obtain ⟨hKE, hCZ⟩ := hCol F K d x hc τ hτ a ha {i} {j} i (by simp) j (by simp)
  have hG := (hGood F K d x hc a).1
  let π : K ⊗[ℂ] K →ₐ[ℂ] K := Algebra.TensorProduct.lmul' ℂ
  have hπX : ∀ b, π ((sysZ K x a).X b : K ⊗[ℂ] K) = algebraMap F K (x b) := by
    intro b
    simp [π, sysZ]
  have hπY : ∀ b, π ((sysZ K x a).Y b : K ⊗[ℂ] K) = algebraMap F K (x b) := by
    intro b
    simp [π, sysZ]
  have hmu : ∀ l, π ((sysZ K x a).mu l) = 0 := by
    intro l
    simp only [Sys.mu, map_sub, map_mul, hπX, hπY]
    ring
  have hv : (π : K ⊗[ℂ] K →+* K) (((sysZ K x a).X i : K ⊗[ℂ] K) ^ d *
      (((∏ b ∈ ({i} : Finset (Fin (d + 1)))ᶜ, (sysZ K x a).X b)⁻¹ : (K ⊗[ℂ] K)ˣ) : K ⊗[ℂ] K)) *
      algebraMap F K (omG x i) = 1 := by
    obtain ⟨P, hPdef⟩ : ∃ P : (K ⊗[ℂ] K)ˣ, P = ∏ b ∈ ({i} : Finset (Fin (d + 1)))ᶜ, (sysZ K x a).X b := ⟨_, rfl⟩
    rw [← hPdef]
    show π (((sysZ K x a).X i : K ⊗[ℂ] K) ^ d * ((P⁻¹ : (K ⊗[ℂ] K)ˣ) : K ⊗[ℂ] K)) * _ = 1
    have hP1 : π (P : K ⊗[ℂ] K) * π ((P⁻¹ : (K ⊗[ℂ] K)ˣ) : K ⊗[ℂ] K) = 1 := by
      rw [← map_mul, Units.mul_inv, map_one]
    have hP2 : π (P : K ⊗[ℂ] K) = ∏ b ∈ ({i} : Finset (Fin (d + 1)))ᶜ, algebraMap F K (x b) := by
      rw [hPdef, Units.coe_prod, map_prod]
      exact Finset.prod_congr rfl fun b _ => hπX b
    have hxi : algebraMap F K (x i) ≠ 0 := by
      simp
    have hom : algebraMap F K (omG x i) =
        algebraMap F K (x i) * (∏ b ∈ ({i} : Finset (Fin (d + 1)))ᶜ, algebraMap F K (x b)) /
          algebraMap F K (x i) ^ (d + 1) := by
      simp only [omG, map_prod, map_div₀, Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ,
        Fintype.card_fin]
      rw [Fintype.prod_eq_mul_prod_compl i, map_pow]
    rw [hom, ← hP2, map_mul, map_pow, hπX]
    have e1 : algebraMap F K (x i) * π (P : K ⊗[ℂ] K) / algebraMap F K (x i) ^ (d + 1) *
        algebraMap F K (x i) ^ d = π (P : K ⊗[ℂ] K) := by
      rw [pow_succ]
      field_simp
    calc _ = π ((P⁻¹ : (K ⊗[ℂ] K)ˣ) : K ⊗[ℂ] K) * (algebraMap F K (x i) * π (P : K ⊗[ℂ] K) /
          algebraMap F K (x i) ^ (d + 1) * algebraMap F K (x i) ^ d) := by ring
      _ = 1 := by rw [e1, mul_comm, hP1]
  have hAdm : (sysZ K x a).admitted n z := by
    have hX : (sysZ K x a).X = (sysZ K x 0).X := rfl
    have hY : (sysZ K x a).Y = (sysZ K x 0).Y := rfl
    have hR : (sysZ K x a).R = (sysZ K x 0).R := rfl
    intro i' j' l
    have h := hz.adm i' j' l
    simp only [Sys.r, Sys.u] at h ⊢
    rw [hX, hY, hR]
    exact h
  obtain ⟨c, hc1, hc2⟩ := core hK2E hK2I hKS hRS hM hML hB hU (sysZ K x a) hG n z hAdm
    (π : K ⊗[ℂ] K →+* K) (Acts (F := F) K τ a) (fun _ _ _ _ h h' => (hAL1 _ _ _ _ h h').1)
    (fun _ _ s h => hAL2 _ _ s h) i j (fun w _ h => hAL4 w _ _ i j h) hKE hCZ hz.diag hmu m hmM _ hm hv
  refine ⟨c, hc1, fun L hL => ?_⟩
  have hk := hKap F K d x hc _ _ (sysZ K x a) π hπX hπY i L hL
  have h := hc2 L hL
  rw [show (π : K ⊗[ℂ] K →+* K) (detC (sysZ K x a).rowMu (uni {i} L)) = kap K x L from hk] at h
  exact h
