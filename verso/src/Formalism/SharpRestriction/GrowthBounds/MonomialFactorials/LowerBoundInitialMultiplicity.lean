import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.UTopVal

noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Finset Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.MainNotions.G.CountingStatementReduction

variable {C0 CE1 CE2 : ℝ} {X : flipOneThree.Inst}

section N0

variable (hS : SegFacts C0 CE1 CE2 X)
include hS

/- English proof (translation)
Break down `le_total j w with h | h` into its components or cases. Rewrite using `[Nat.cast_sub h]`. Rewrite using `[Nat.sub_eq_zero_of_le h, Nat.cast_zero]`. Establish `: (w : ℝ) ≤ j` using `by exact_mod_cast h`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem cast_sub_ge (w j : ℕ) : (w : ℝ) - j ≤ ((w - j : ℕ) : ℝ) := by
  rcases le_total j w with h | h
  · rw [Nat.cast_sub h]
  · rw [Nat.sub_eq_zero_of_le h, Nat.cast_zero]
    have : (w : ℝ) ≤ j := by exact_mod_cast h
    linarith

/- English proof (translation)
Take `⟨hK, hdl, hlv⟩` from `digits_of_idx hx`. Establish `hK'` using `hK`. Take `⟨hDig, hK1, -, -⟩` from `hK'`. Use `set u := uTop (X.S C0 CE1 CE2) i with hu`. Establish `hσu : (X.S C0 CE1 CE2).sigma ≤ (u : ℕ)`.

Simplify using `[hu, uTop]`. Use `set P := SegData.P X.p (X.S C0 CE1 CE2) u with hPdef`. Establish `hPpos : 0 < P` using `twoPow_pos C0 CE1 CE2 X u`. Establish `hj : x.2.1 i ≤ x.1.o u` using `(((mem_lv _ _ _).mp hlv).1 i).1`. Establish `hA : coarseA X.p (X.S C0 CE1 CE2) x.1 u ≤ (X.S C0 CE1 CE2).bTop u / P` using `Nat.div_le_div_right (Nat.sub_le _ _)`.

Establish `hjP : x.2.1 i * P ≤ (X.S C0 CE1 CE2).bTop u` using `(Nat.mul_le_mul_right _ ((hj.trans (hK1 u hσu).1).trans hA)).trans (Nat.div_mul_le_self _ _)`. Establish `hry : x.1.ry = dl.2` using `by rw [← hdl]`. Establish `hne : (Nl C0 CE1 CE2 X dl x.2 i).Nonempty` using `(Wl_ne ha u).image _`. Establish `hn0 : (XMof C0 CE1 CE2 X dl a x.1 x.2).n₀ i = sInf (↑(Nl C0 CE1 CE2 X dl x.2 i) : Set ℕ)` using `rfl`. Establish `hmem : sInf (↑(Nl C0 CE1 CE2 X dl x.2 i) : Set ℕ) ∈ (↑(Nl C0 CE1 CE2 X dl x.2 i) : Set ℕ)` using `Nat.sInf_mem (Finset.coe_nonempty.mpr hne)`.

Rewrite `hmem` using `[Finset.mem_coe]`. Take `⟨v, hv, hcm⟩` from `Finset.mem_image.mp hmem`. Simplify using `only [Wl, Finset.mem_filter, flipOneThree.Inst.winA, Finset.mem_Icc] at hv`. Take `⟨⟨hav, -⟩, hsv, hdvd⟩` from `hv`. Rewrite `hsv`, `hdvd` using `[← hu]`.

Rewrite using `[hn0, ← hcm]`. Establish `hsum : ∑ c : Fin (X.r + 1), dl.2 u c ≤ (X.r + 1) * P`. Combine the equalities or inequalities in the displayed calculation. Apply `Finset.sum_le_sum` to reduce the goal to its premises. Introduce `c _`.

Rewrite using `[← hry]`. Conclude with `le_of_lt (hDig.1 u c).2`. Use `_ = (X.r + 1) * P := by simp`. Establish `hQ : (v - ∑ c : Fin (X.r + 1), dl.2 u c) / P * P = v - ∑ c : Fin (X.r + 1), dl.2 u c` using `Nat.div_mul_cancel hdvd`. Establish `hc1` using `cast_sub_ge hS ((v - ∑ c : Fin (X.r + 1), dl.2 u c) / P) (x.2.1 i)`.

Establish `hcm' : cm C0 CE1 CE2 X dl x.2 i v = (v - ∑ c : Fin (X.r + 1), dl.2 u c) / P - x.2.1 i` using `rfl`. Rewrite using `[hcm']`. Establish `hQr : (((v - ∑ c : Fin (X.r + 1), dl.2 u c) / P : ℕ) : ℝ) * (P : ℝ) = (v : ℝ) - (∑ c : Fin (X.r + 1), dl.2 u c : ℕ)`. Rewrite using `[← Nat.cast_sub hsv, ← Nat.cast_mul, hQ]`. Establish `hsumR : ((∑ c : Fin (X.r + 1), dl.2 u c : ℕ) : ℝ) ≤ ((X.r : ℝ) + 1) * (P : ℝ)`.

Conclude with `hsum` after adjusting the coercions. Establish `hjPR : ((x.2.1 i : ℕ) : ℝ) * (P : ℝ) ≤ 5 / 2 * X.L.b'`. Establish `h1 : (((x.2.1 i * P : ℕ)) : ℝ) ≤ (X.S C0 CE1 CE2).bTop u` using `by exact_mod_cast hjP`. Move the coercions through the operations in `at h1`. Combine the linear relations using `[hS.bTop u]`.

Establish `havR : (X.L.a : ℝ) ≤ v` using `by exact_mod_cast hav`. Establish `hPR : (0 : ℝ) ≤ (P : ℝ)` using `Nat.cast_nonneg _`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem lower_bound_initial_multiplicity {dl : DCl X} {a : Fin X.s → ℕ} (ha : a ∈ cbox C0 CE1 CE2 X dl)
    {x : Σ _ : SegBlock X.s X.r, Lv C0 CE1 CE2 X} (hx : x ∈ idx C0 CE1 CE2 X dl a) (i : Fin (X.S C0 CE1 CE2).t) :
    (X.L.a : ℝ) - ((X.r : ℝ) + 1) * ((X.S C0 CE1 CE2).P X.p (uTop (X.S C0 CE1 CE2) i) : ℝ) - 5 / 2 * X.L.b' ≤
      ((XMof C0 CE1 CE2 X dl a x.1 x.2).n₀ i : ℝ) * ((X.S C0 CE1 CE2).P X.p (uTop (X.S C0 CE1 CE2) i) : ℝ) := by
  obtain ⟨hK, hdl, hlv⟩ := digits_of_idx hx
  have hK' := hK
  obtain ⟨hDig, hK1, -, -⟩ := hK'
  set u := uTop (X.S C0 CE1 CE2) i with hu
  have hσu : (X.S C0 CE1 CE2).sigma ≤ (u : ℕ) := by
    simp [hu, uTop]
  set P := SegData.P X.p (X.S C0 CE1 CE2) u with hPdef
  have hPpos : 0 < P := twoPow_pos C0 CE1 CE2 X u
  have hj : x.2.1 i ≤ x.1.o u := (((mem_lv _ _ _).mp hlv).1 i).1
  have hA : coarseA X.p (X.S C0 CE1 CE2) x.1 u ≤ (X.S C0 CE1 CE2).bTop u / P :=
    Nat.div_le_div_right (Nat.sub_le _ _)
  have hjP : x.2.1 i * P ≤ (X.S C0 CE1 CE2).bTop u :=
    (Nat.mul_le_mul_right _ ((hj.trans (hK1 u hσu).1).trans hA)).trans (Nat.div_mul_le_self _ _)
  have hry : x.1.ry = dl.2 := by rw [← hdl]
  have hne : (Nl C0 CE1 CE2 X dl x.2 i).Nonempty := (Wl_ne ha u).image _
  have hn0 : (XMof C0 CE1 CE2 X dl a x.1 x.2).n₀ i = sInf (↑(Nl C0 CE1 CE2 X dl x.2 i) : Set ℕ) := rfl
  have hmem : sInf (↑(Nl C0 CE1 CE2 X dl x.2 i) : Set ℕ) ∈ (↑(Nl C0 CE1 CE2 X dl x.2 i) : Set ℕ) :=
    Nat.sInf_mem (Finset.coe_nonempty.mpr hne)
  rw [Finset.mem_coe] at hmem
  obtain ⟨v, hv, hcm⟩ := Finset.mem_image.mp hmem
  simp only [Wl, Finset.mem_filter, flipOneThree.Inst.winA, Finset.mem_Icc] at hv
  obtain ⟨⟨hav, -⟩, hsv, hdvd⟩ := hv
  rw [← hu] at hsv hdvd
  rw [hn0, ← hcm]
  have hsum : ∑ c : Fin (X.r + 1), dl.2 u c ≤ (X.r + 1) * P := by
    calc ∑ c : Fin (X.r + 1), dl.2 u c ≤ ∑ _c : Fin (X.r + 1), P := by
          apply Finset.sum_le_sum
          intro c _
          rw [← hry]
          exact le_of_lt (hDig.1 u c).2
      _ = (X.r + 1) * P := by simp
  have hQ : (v - ∑ c : Fin (X.r + 1), dl.2 u c) / P * P = v - ∑ c : Fin (X.r + 1), dl.2 u c :=
    Nat.div_mul_cancel hdvd
  have hc1 := cast_sub_ge hS ((v - ∑ c : Fin (X.r + 1), dl.2 u c) / P) (x.2.1 i)
  have hcm' : cm C0 CE1 CE2 X dl x.2 i v = (v - ∑ c : Fin (X.r + 1), dl.2 u c) / P - x.2.1 i := rfl
  rw [hcm']
  have hQr : (((v - ∑ c : Fin (X.r + 1), dl.2 u c) / P : ℕ) : ℝ) * (P : ℝ) =
      (v : ℝ) - (∑ c : Fin (X.r + 1), dl.2 u c : ℕ) := by
    rw [← Nat.cast_sub hsv, ← Nat.cast_mul, hQ]
  have hsumR : ((∑ c : Fin (X.r + 1), dl.2 u c : ℕ) : ℝ) ≤ ((X.r : ℝ) + 1) * (P : ℝ) := by
    exact_mod_cast hsum
  have hjPR : ((x.2.1 i : ℕ) : ℝ) * (P : ℝ) ≤ 5 / 2 * X.L.b' := by
    have h1 : (((x.2.1 i * P : ℕ)) : ℝ) ≤ (X.S C0 CE1 CE2).bTop u := by exact_mod_cast hjP
    push_cast at h1
    linarith [hS.bTop u]
  have havR : (X.L.a : ℝ) ≤ v := by exact_mod_cast hav
  have hPR : (0 : ℝ) ≤ (P : ℝ) := Nat.cast_nonneg _
  nlinarith

/- English proof (translation)
Introduce `dl hdl a ha x hx i`. Establish `hF` using `hS.hF`. Establish `hinj : Function.Injective (uTop (X.S C0 CE1 CE2))`. Introduce `k k' h`. Simplify using `only [uTop, Fin.mk.injEq] at h`.

Conclude with `Fin.ext (by omega)`. Use `set n : Fin (X.S C0 CE1 CE2).t → ℕ := fun k => topA C0 CE1 CE2 X dl (uTop (X.S C0 CE1 CE2) k) with hn`. Use `set a' := ovr (uTop (X.S C0 CE1 CE2)) a n with haeq`. Establish `ha' : a' ∈ cbox C0 CE1 CE2 X dl`. Establish `hb` using `cbox_eq C0 CE1 CE2 X dl a ha`.

Rewrite using `[hb]`. Apply `ovr_mem _ hinj` to reduce the goal to its premises. Rewrite using `[← hb]`. Conclude with `ha`. Conclude with `Fintype.mem_piFinset.mpr (fun k => topA_mem_Wl ha _)`.

Establish `hx' : x ∈ idx C0 CE1 CE2 X dl a'`. Rewrite using `[← hFree dl hdl a ha a' ha']`. Conclude with `hx`. Take `⟨hK', -, -⟩` from `digits_of_idx hx'`. Take `⟨-, hdl0, -⟩` from `digits_of_idx hx`.

Establish `hry : x.1.ry = dl.2` using `by rw [← hdl0]`. Establish `hT'` using `(mem_cbox' ha').1`. Establish `hSb` using `S_bound hS a' hT' x.1 hK' x.2 i`. Establish `hn0` using `lower_bound_initial_multiplicity hS ha hx i`. Establish `htop : (XMof C0 CE1 CE2 X dl a x.1 x.2).top = fun k => (n k - ∑ c : Fin (X.r + 1), x.1.ry (uTop (X.S C0 CE1 CE2) k) c) / SegData.P X.p (X.S C0 CE1 CE2) (uTop (X.S C0 CE1 CE2) k) - x.2.1 k`.

Use function extensionality and compare the values at `k`. Establish `hne : (Nl C0 CE1 CE2 X dl x.2 k).Nonempty` using `(Wl_ne ha _).image _`. Establish `h1` using `cm_top (dl := dl) x.2 k (Wl_ne ha _)`. Establish `h2 : sInf (↑(Nl C0 CE1 CE2 X dl x.2 k) : Set ℕ) ≤ (Nl C0 CE1 CE2 X dl x.2 k).sup id`. Establish `hm` using `Nat.sInf_mem (Finset.coe_nonempty.mpr hne)`.

Conclude with `Finset.le_sup (f := id) hm`. Rewrite using `[hry]`. Use `show sInf (↑(Nl C0 CE1 CE2 X dl x.2 k) : Set ℕ) + 1 * ((Nl C0 CE1 CE2 X dl x.2 k).sup id - sInf (↑(Nl C0 CE1 CE2 X dl x.2 k) : Set ℕ) + 1 - 1) = cm C0 CE1 CE2 X dl x.2 k (n k)`. Rewrite using `[h1]`. Use linear arithmetic over natural numbers and integers.

Establish `hL : (XMof C0 CE1 CE2 X dl a x.1 x.2).LL.setTies (XMof C0 CE1 CE2 X dl a x.1 x.2).T (XMof C0 CE1 CE2 X dl a x.1 x.2).top = lLL C0 CE1 CE2 X a' x.1 x.2`. Rewrite using `[htop, haeq, lLL_ovr]`. Both sides reduce to the same expression. Establish `hP : (0 : ℝ) < (SegData.P X.p (X.S C0 CE1 CE2) (uTop (X.S C0 CE1 CE2) i) : ℝ)`. Conclude with `twoPow_pos C0 CE1 CE2 X _` after adjusting the coercions.

Establish `hkP` using `hS.kP (uTop (X.S C0 CE1 CE2) i)`. Establish `hm' : (4 : ℝ) ≤ X.L.m` using `by exact_mod_cast hF.m4`. Establish `hsm : (2 * (X.s : ℝ) + 2) ≤ X.L.m` using `by exact_mod_cast hF.s_le`. Establish `hpm` using `hF.p_ge`. Establish `hp0 : (0 : ℝ) < X.p` using `by show (0 : ℝ) < X.L.p`.

Use the polynomial consequences of the given equalities and inequalities. Establish `h48 : (4 * (X.s : ℝ) + 8) ≤ X.p` using `by show (4 * (X.s : ℝ) + 8) ≤ X.L.p`. Use the polynomial consequences of the given equalities and inequalities. Establish `hb'p : X.L.b' ≤ (X.L.a : ℝ) / X.p`. Rewrite using `[le_div_iff₀ hp0]`.

Use `hF.b_lt` as an intermediate fact. Use `show X.L.b' * X.L.p ≤ X.L.a`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `ha0 : (0 : ℝ) ≤ X.L.a` using `Nat.cast_nonneg _`. Establish `hsum : (2 * (X.s : ℝ) + 1) * (2 * X.L.a / X.p) + 6 * ((X.L.a : ℝ) / X.p) ≤ X.L.a`.

Combine the equalities or inequalities in the displayed calculation. Establish `hreal : ((GM.M.TieData.S (lLL C0 CE1 CE2 X a' x.1 x.2) (gT C0 CE1 CE2 X x.1) i : ℕ) : ℝ) * (SegData.P X.p (X.S C0 CE1 CE2) (uTop (X.S C0 CE1 CE2) i) : ℝ) ≤ ((XMof C0 CE1 CE2 X dl a x.1 x.2).n₀ i : ℝ) * (SegData.P X.p (X.S C0 CE1 CE2) (uTop (X.S C0 CE1 CE2) i) : ℝ)`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hnat : GM.M.TieData.S (lLL C0 CE1 CE2 X a' x.1 x.2) (gT C0 CE1 CE2 X x.1) i ≤ (XMof C0 CE1 CE2 X dl a x.1 x.2).n₀ i`. Conclude with `le_of_mul_le_mul_right hreal hP` after adjusting the coercions.

Rewrite using `[hL]`. Conclude with `hnat`.
-/
theorem restSI_proved (hFree : RestFree C0 CE1 CE2 X) : RestSI (C0 := C0) (CE1 := CE1) (CE2 := CE2) (X := X) := by
  intro dl hdl a ha x hx i
  have hF := hS.hF
  have hinj : Function.Injective (uTop (X.S C0 CE1 CE2)) := by
    intro k k' h
    simp only [uTop, Fin.mk.injEq] at h
    exact Fin.ext (by omega)
  set n : Fin (X.S C0 CE1 CE2).t → ℕ := fun k => topA C0 CE1 CE2 X dl (uTop (X.S C0 CE1 CE2) k) with hn
  set a' := ovr (uTop (X.S C0 CE1 CE2)) a n with haeq
  have ha' : a' ∈ cbox C0 CE1 CE2 X dl := by
    have hb := cbox_eq C0 CE1 CE2 X dl a ha
    rw [hb]
    apply ovr_mem _ hinj
    · rw [← hb]
      exact ha
    · exact Fintype.mem_piFinset.mpr (fun k => topA_mem_Wl ha _)
  have hx' : x ∈ idx C0 CE1 CE2 X dl a' := by
    rw [← hFree dl hdl a ha a' ha']
    exact hx
  obtain ⟨hK', -, -⟩ := digits_of_idx hx'
  obtain ⟨-, hdl0, -⟩ := digits_of_idx hx
  have hry : x.1.ry = dl.2 := by rw [← hdl0]
  have hT' := (mem_cbox' ha').1
  have hSb := S_bound hS a' hT' x.1 hK' x.2 i
  have hn0 := lower_bound_initial_multiplicity hS ha hx i
  have htop : (XMof C0 CE1 CE2 X dl a x.1 x.2).top = fun k =>
      (n k - ∑ c : Fin (X.r + 1), x.1.ry (uTop (X.S C0 CE1 CE2) k) c) /
        SegData.P X.p (X.S C0 CE1 CE2) (uTop (X.S C0 CE1 CE2) k) - x.2.1 k := by
    funext k
    have hne : (Nl C0 CE1 CE2 X dl x.2 k).Nonempty := (Wl_ne ha _).image _
    have h1 := cm_top (dl := dl) x.2 k (Wl_ne ha _)
    have h2 : sInf (↑(Nl C0 CE1 CE2 X dl x.2 k) : Set ℕ) ≤ (Nl C0 CE1 CE2 X dl x.2 k).sup id := by
      have hm := Nat.sInf_mem (Finset.coe_nonempty.mpr hne)
      exact Finset.le_sup (f := id) hm
    rw [hry]
    show sInf (↑(Nl C0 CE1 CE2 X dl x.2 k) : Set ℕ) +
        1 * ((Nl C0 CE1 CE2 X dl x.2 k).sup id - sInf (↑(Nl C0 CE1 CE2 X dl x.2 k) : Set ℕ) + 1 - 1) =
      cm C0 CE1 CE2 X dl x.2 k (n k)
    rw [h1]
    omega
  have hL : (XMof C0 CE1 CE2 X dl a x.1 x.2).LL.setTies (XMof C0 CE1 CE2 X dl a x.1 x.2).T
      (XMof C0 CE1 CE2 X dl a x.1 x.2).top = lLL C0 CE1 CE2 X a' x.1 x.2 := by
    rw [htop, haeq, lLL_ovr]
    rfl
  have hP : (0 : ℝ) < (SegData.P X.p (X.S C0 CE1 CE2) (uTop (X.S C0 CE1 CE2) i) : ℝ) := by
    exact_mod_cast twoPow_pos C0 CE1 CE2 X _
  have hkP := hS.kP (uTop (X.S C0 CE1 CE2) i)
  have hm' : (4 : ℝ) ≤ X.L.m := by exact_mod_cast hF.m4
  have hsm : (2 * (X.s : ℝ) + 2) ≤ X.L.m := by exact_mod_cast hF.s_le
  have hpm := hF.p_ge
  have hp0 : (0 : ℝ) < X.p := by
    show (0 : ℝ) < X.L.p
    nlinarith
  have h48 : (4 * (X.s : ℝ) + 8) ≤ X.p := by
    show (4 * (X.s : ℝ) + 8) ≤ X.L.p
    nlinarith
  have hb'p : X.L.b' ≤ (X.L.a : ℝ) / X.p := by
    rw [le_div_iff₀ hp0]
    have := hF.b_lt
    show X.L.b' * X.L.p ≤ X.L.a
    linarith
  have ha0 : (0 : ℝ) ≤ X.L.a := Nat.cast_nonneg _
  have hsum : (2 * (X.s : ℝ) + 1) * (2 * X.L.a / X.p) + 6 * ((X.L.a : ℝ) / X.p) ≤ X.L.a := by
    calc (2 * (X.s : ℝ) + 1) * (2 * X.L.a / X.p) + 6 * ((X.L.a : ℝ) / X.p)
        = (4 * (X.s : ℝ) + 8) * ((X.L.a : ℝ) / X.p) := by ring
      _ ≤ (X.p : ℝ) * ((X.L.a : ℝ) / X.p) := mul_le_mul_of_nonneg_right h48 (by positivity)
      _ = X.L.a := by field_simp
  have hreal : ((GM.M.TieData.S (lLL C0 CE1 CE2 X a' x.1 x.2) (gT C0 CE1 CE2 X x.1) i : ℕ) : ℝ) *
        (SegData.P X.p (X.S C0 CE1 CE2) (uTop (X.S C0 CE1 CE2) i) : ℝ) ≤
      ((XMof C0 CE1 CE2 X dl a x.1 x.2).n₀ i : ℝ) *
        (SegData.P X.p (X.S C0 CE1 CE2) (uTop (X.S C0 CE1 CE2) i) : ℝ) := by
    linarith
  have hnat : GM.M.TieData.S (lLL C0 CE1 CE2 X a' x.1 x.2) (gT C0 CE1 CE2 X x.1) i ≤
      (XMof C0 CE1 CE2 X dl a x.1 x.2).n₀ i := by
    exact_mod_cast le_of_mul_le_mul_right hreal hP
  rw [hL]
  exact hnat

/- English proof (translation)
The claim follows from `restTMSize_of hS hFree (restSI_proved hS hFree)`.
-/
theorem restTMSize_proved (hFree : RestFree C0 CE1 CE2 X) : RestTMSize C0 CE1 CE2 X :=
  restTMSize_of hS hFree (restSI_proved hS hFree)

end N0

end Formalism.MainNotions.G.SymmetricFormBlocks

end
