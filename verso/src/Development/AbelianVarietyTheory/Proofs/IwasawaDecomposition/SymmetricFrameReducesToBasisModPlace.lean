import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemUnipSymBc
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.KppFrameW
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.RowDictPf
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.Mem.SymFrameRed

open Formalism.MainNotions.S Formalism.L2.SG.Pf.RowDictPf PIW.AdelClassFin Formalism.L2.SG.Pf.RedBasicsPf Formalism.L2.SG.Pf.unitaryCongruence
  Formalism.L2.SG.Pf.AllRowsRedKerA Formalism.L2.SG.Pf.KppRedW Formalism.L2.SG.Pf.AllRowsRho Formalism.L2.SG.Pf.KppFrameW

/- English proof (translation)
Substitute `hn` using the available equality. Take `⟨i, hi⟩` from `i`. Take `⟨j, hj⟩` from `j`. Simplify using `only [GlobalTheory.SeeConjRead.flagV, Fin.mk.injEq]`. Apply the tactic sequence `split_ifs <;> first`.

Consider the case `(exfalso; omega)`. Consider the case `(rw [sub_zero]; first | exact heb _ _ | exact hez _ | exact hef _ _ | exact hbe _ _ | exact hbz _ | exact hbf _ _ | exact hze _ | exact hzb _ | exact hzf _ | exact hfe _ _ | exact hfb _ _ | exact hfz _)`. Consider the case `exact hzz`. Consider the case `(convert hee _ _ using 2; simp only [Fin.mk.injEq]; split_ifs <;> first | rfl | (exfalso; omega))`. Consider the case `(convert hbb _ _ using 2; simp only [Fin.mk.injEq]; split_ifs <;> first | rfl | (exfalso; omega))`.

Consider the case `(convert hff _ _ using 2; simp only [Fin.mk.injEq]; split_ifs <;> first | rfl | (exfalso; omega))`.
-/
theorem gram_flagV {M R : Type} [Zero M] [Ring R] (S : AddSubgroup R) (B : M → M → R) {ρ k n : ℕ}
    (hn : n = 2 * ρ + k + 1) (e f e' f' : Fin ρ → M) (b b' : Fin k → M) (z z' : M)
    (hee : ∀ a c, B (e' a) (e c) - (if a = c then 1 else 0) ∈ S)
    (heb : ∀ a j, B (e' a) (b j) ∈ S) (hez : ∀ a, B (e' a) z ∈ S) (hef : ∀ a c, B (e' a) (f c) ∈ S)
    (hbe : ∀ i c, B (b' i) (e c) ∈ S) (hbb : ∀ i j, B (b' i) (b j) - (if i = j then 1 else 0) ∈ S)
    (hbz : ∀ i, B (b' i) z ∈ S) (hbf : ∀ i c, B (b' i) (f c) ∈ S)
    (hze : ∀ c, B z' (e c) ∈ S) (hzb : ∀ j, B z' (b j) ∈ S) (hzz : B z' z - 1 ∈ S) (hzf : ∀ c, B z' (f c) ∈ S)
    (hfe : ∀ a c, B (f' a) (e c) ∈ S) (hfb : ∀ a j, B (f' a) (b j) ∈ S) (hfz : ∀ a, B (f' a) z ∈ S)
    (hff : ∀ a c, B (f' a) (f c) - (if a = c then 1 else 0) ∈ S) (i j : Fin n) :
    B (GlobalTheory.SeeConjRead.flagV ρ k n e' f' b' z' i) (GlobalTheory.SeeConjRead.flagV ρ k n e f b z j) -
      (if i = j then 1 else 0) ∈ S := by
  subst hn
  obtain ⟨i, hi⟩ := i
  obtain ⟨j, hj⟩ := j
  simp only [GlobalTheory.SeeConjRead.flagV, Fin.mk.injEq]
  split_ifs <;> first
    | (exfalso; omega)
    | (rw [sub_zero]; first | exact heb _ _ | exact hez _ | exact hef _ _ | exact hbe _ _ | exact hbz _ | exact hbf _ _ | exact hze _ | exact hzb _ | exact hzf _ | exact hfe _ _ | exact hfb _ _ | exact hfz _)
    | exact hzz
    | (convert hee _ _ using 2; simp only [Fin.mk.injEq]; split_ifs <;> first | rfl | (exfalso; omega))
    | (convert hbb _ _ using 2; simp only [Fin.mk.injEq]; split_ifs <;> first | rfl | (exfalso; omega))
    | (convert hff _ _ using 2; simp only [Fin.mk.injEq]; split_ifs <;> first | rfl | (exfalso; omega))

/- English proof (translation)
Unfold `GlobalTheory.SeeConjRead.flagV`. Use `split_ifs`. Conclude with `he _`. Conclude with `hb _`. Conclude with `hz`.

Conclude with `hf _`. Conclude with `h0`.
-/
theorem flagV_mem {M : Type} [Zero M] (P : M → Prop) (h0 : P 0) {ρ k n : ℕ} {e f : Fin ρ → M} {b : Fin k → M}
    {z : M} (he : ∀ a, P (e a)) (hf : ∀ a, P (f a)) (hb : ∀ i, P (b i)) (hz : P z) (i : Fin n) :
    P (GlobalTheory.SeeConjRead.flagV ρ k n e f b z i) := by
  unfold GlobalTheory.SeeConjRead.flagV
  split_ifs
  · exact he _
  · exact hb _
  · exact hz
  · exact hf _
  · exact h0

/- English proof (translation)
Take `⟨t, ht⟩` from `D.R.m_even`. Establish `h2` using `D.R.two_le_m`. Unfold `Ranks.r Ranks.rS`. Use linear arithmetic over natural numbers and integers.
-/
theorem r_eq (D : D7) : D.R.r = 2 * D.R.rS + D.R.k + 1 := by
  obtain ⟨t, ht⟩ := D.R.m_even
  have h2 := D.R.two_le_m
  unfold Ranks.r Ranks.rS
  omega

/- English proof (translation)
Establish `h0 : hhat I 0 v = 0`. Use `hhat_sub_left I u u v` as an intermediate fact. Rewrite `this` using `[sub_self, sub_self]`. Then use the resulting hypothesis. Use `hhat_sub_left I 0 u v` as an intermediate fact. Rewrite `this` using `[zero_sub, h0, zero_sub]`. Then use the resulting hypothesis.
-/
theorem hhat_neg (I : AutInst) (u v : Fin I.n → I.E ⊗[I.F] Af I.F) : hhat I (-u) v = -hhat I u v := by
  have h0 : hhat I 0 v = 0 := by
    have := hhat_sub_left I u u v
    rwa [sub_self, sub_self] at this
  have := hhat_sub_left I 0 u v
  rwa [zero_sub, h0, zero_sub] at this

/- English proof (translation)
Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem sg_ite (I : AutInst) (q : Prop) [Decidable q] (x : I.E ⊗[I.F] Af I.F) :
    sg I (if q then x else 0) = if q then sg I x else 0 := by
  split_ifs <;> simp

variable {D : D7}

/- English proof (translation)
Unfold `wLf Lq`. Rewrite using `[wLat_eq]`.
-/
theorem wLf_eq (X : HidaSetting D) (w : HeightOneSpectrum (𝓞 D.host.E)) : wLf X w = Lq X.B.I (wB X w) := by
  unfold wLf Lq
  rw [wLat_eq]

/- English proof (translation)
Use `show RingOfIntegers.mapRingEquiv X.ιE ((X.B.g : ℕ) : 𝓞 X.B.I.E) ∈ (D.naut.plGw kv.1 kv.2).asIdeal`. Rewrite using `[map_natCast]`. Conclude with `level_mem X kv`.
-/
theorem natCast_wB (X : HidaSetting D) (kv : Σ k : Fin 2, D.nd.PlG k) :
    ((X.B.g : ℕ) : 𝓞 X.B.I.E) ∈ (wB X (D.naut.plGw kv.1 kv.2)).asIdeal := by
  show RingOfIntegers.mapRingEquiv X.ιE ((X.B.g : ℕ) : 𝓞 X.B.I.E) ∈ (D.naut.plGw kv.1 kv.2).asIdeal
  rw [map_natCast]
  exact level_mem X kv

/- English proof (translation)
Use `iE_mem (I := X.B.I) (natCast_wB X kv)` as an intermediate fact. Simplify `this` using `[iE]`.
-/
theorem g_Wq (X : HidaSetting D) (kv : Σ k : Fin 2, D.nd.PlG k) :
    ((X.B.g : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) ∈ Wq X.B.I (wB X (D.naut.plGw kv.1 kv.2)) := by
  have := iE_mem (I := X.B.I) (natCast_wB X kv)
  simpa [iE] using this

/- English proof (translation)
Take `⟨t, ht, rfl⟩` from `hc`. Conclude with `Wq_mul' (g_Wq X kv) ht`.
-/
theorem zmod_Wq (X : HidaSetting D) (kv : Σ k : Fin 2, D.nd.PlG k) {c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F}
    (hc : ZMod' X.B.I X.B.g c) : c ∈ Wq X.B.I (wB X (D.naut.plGw kv.1 kv.2)) := by
  obtain ⟨t, ht, rfl⟩ := hc
  exact Wq_mul' (g_Wq X kv) ht

/- English proof (translation)
Take `⟨t, ht, rfl⟩` from `hc`. Conclude with `⟨sg X.B.I t, DictLat.sigR_int X.B.I ht, by rw [map_mul, sg_natCast]⟩`.
-/
theorem zmod_sg (X : HidaSetting D) {c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F} (hc : ZMod' X.B.I X.B.g c) :
    ZMod' X.B.I X.B.g (sg X.B.I c) := by
  obtain ⟨t, ht, rfl⟩ := hc
  exact ⟨sg X.B.I t, DictLat.sigR_int X.B.I ht, by rw [map_mul, sg_natCast]⟩

/- English proof (translation)
Establish `h1` using `zmod_Wq X kv (zmod_sg X h)`. Establish `e : sg X.B.I (hA X.B.I x y) = hhat X.B.I y x` using `hhat_conj X.B.I x y`. Rewrite `h1` using `[map_sub, e]`. Then use the resulting hypothesis.
-/
theorem sw (X : HidaSetting D) (kv : Σ k : Fin 2, D.nd.PlG k) {x y : VA X.B.I} {d : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F}
    (h : ZMod' X.B.I X.B.g (hA X.B.I x y - d)) :
    hhat X.B.I y x - sg X.B.I d ∈ Wq X.B.I (wB X (D.naut.plGw kv.1 kv.2)) := by
  have h1 := zmod_Wq X kv (zmod_sg X h)
  have e : sg X.B.I (hA X.B.I x y) = hhat X.B.I y x := hhat_conj X.B.I x y
  rwa [map_sub, e] at h1

/- English proof (translation)
Use `sw X kv (d := 0) (by rwa [sub_zero])` as an intermediate fact. Rewrite `this` using `[map_zero, sub_zero]`. Then use the resulting hypothesis.
-/
theorem sw0 (X : HidaSetting D) (kv : Σ k : Fin 2, D.nd.PlG k) {x y : VA X.B.I}
    (h : ZMod' X.B.I X.B.g (hA X.B.I x y)) : hhat X.B.I y x ∈ Wq X.B.I (wB X (D.naut.plGw kv.1 kv.2)) := by
  have := sw X kv (d := 0) (by rwa [sub_zero])
  rwa [map_zero, sub_zero] at this

/- English proof (translation)
Unfold `mL`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨x, hx, rfl⟩`. Conclude with `smul_Lf_wLf X _ _ (level_mem X kv) hx`.
-/
theorem mL_le (X : HidaSetting D) (kv : Σ k : Fin 2, D.nd.PlG k) : mL X.B.I X.B.g ≤ wLf X (D.naut.plGw kv.1 kv.2) := by
  unfold mL
  rw [Submodule.span_le]
  rintro _ ⟨x, hx, rfl⟩
  exact smul_Lf_wLf X _ _ (level_mem X kv) hx

/- English proof (translation)
Rewrite `h` using `[wLf_eq]`. Establish `hz : X.z0 ∈ X.B.I.Lf` using `X.vectorsInLattice.2.1`. Establish `h1` using `hhat_Lq_right hz h`. Rewrite `h1` using `[DictLat.hhat_smul_right]`. Establish `h2 : hhat X.B.I X.z0 X.z0 + 1 ∈ Wq X.B.I (wB X (D.naut.plGw kv.1 kv.2))` using `zmod_Wq X kv X.formsAtZero.1`.

Establish `h3` using `Wq_mul h2 hs`. Establish `e : s = s * (hhat X.B.I X.z0 X.z0 + 1) - s * hhat X.B.I X.z0 X.z0` using `by ring`. Rewrite using `[e]`. Conclude with `sub_mem h3 h1`.
-/
theorem scal_of_vec (X : HidaSetting D) (kv : Σ k : Fin 2, D.nd.PlG k) {s : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F}
    (hs : s ∈ IntAf X.B.I.F X.B.I.E) (h : s • X.z0 ∈ wLf X (D.naut.plGw kv.1 kv.2)) :
    s ∈ Wq X.B.I (wB X (D.naut.plGw kv.1 kv.2)) := by
  rw [wLf_eq] at h
  have hz : X.z0 ∈ X.B.I.Lf := X.vectorsInLattice.2.1
  have h1 := hhat_Lq_right hz h
  rw [DictLat.hhat_smul_right] at h1
  have h2 : hhat X.B.I X.z0 X.z0 + 1 ∈ Wq X.B.I (wB X (D.naut.plGw kv.1 kv.2)) := zmod_Wq X kv X.formsAtZero.1
  have h3 := Wq_mul h2 hs
  have e : s = s * (hhat X.B.I X.z0 X.z0 + 1) - s * hhat X.B.I X.z0 X.z0 := by ring
  rw [e]
  exact sub_mem h3 h1

/- English proof (translation)
Take `⟨c, hc, ht⟩` from `h`. Take `⟨c', hc', ht'⟩` from `h'`. Establish `hd : (p : ℤ) ∣ c - c'` using `(ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).1 (hc'.trans hc.symm)`. Take `⟨q, hq⟩` from `hd`. Establish `hpq : ((c - c' : ℤ) : I.E ⊗[I.F] Af I.F) ∈ Wq I w`.

Rewrite using `[hq, Int.cast_mul, Int.cast_natCast]`. Conclude with `Wq_mul' (natCast_Wq hp hcard) (intCast_int q)`. Establish `e : t - t' = (t - c) - (t' - c') + ((c - c' : ℤ) : I.E ⊗[I.F] Af I.F)` using `by push_cast; ring`. Rewrite using `[e]`. Conclude with `add_mem (sub_mem ht ht') hpq`.
-/
theorem congW_eq_mem {I : AutInst} {w : HeightOneSpectrum (𝓞 I.E)} {p : ℕ} (hp : p.Prime)
    (hcard : Nat.card (𝓞 I.E ⧸ w.asIdeal) = p) {t t' : I.E ⊗[I.F] Af I.F} {m : ZMod p}
    (h : CongW (w := w) p t m) (h' : CongW (w := w) p t' m) : t - t' ∈ Wq I w := by
  obtain ⟨c, hc, ht⟩ := h
  obtain ⟨c', hc', ht'⟩ := h'
  have hd : (p : ℤ) ∣ c - c' := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).1 (hc'.trans hc.symm)
  obtain ⟨q, hq⟩ := hd
  have hpq : ((c - c' : ℤ) : I.E ⊗[I.F] Af I.F) ∈ Wq I w := by
    rw [hq, Int.cast_mul, Int.cast_natCast]
    exact Wq_mul' (natCast_Wq hp hcard) (intCast_int q)
  have e : t - t' = (t - c) - (t' - c') + ((c - c' : ℤ) : I.E ⊗[I.F] Af I.F) := by push_cast; ring
  rw [e]
  exact add_mem (sub_mem ht ht') hpq

/- English proof (translation)
The claim follows from `scal_of_vec X kv (sub_mem (one_mem _) X.ew_int) (hE X.z0 X.vectorsInLattice.2.1)`.
-/
theorem ew_at (X : HidaSetting D) (kv : Σ k : Fin 2, D.nd.PlG k) (hE : GlobalTheory.Mem.SymFrame.EwAt X (D.naut.plGw kv.1 kv.2)) :
    1 - X.ew ∈ Wq X.B.I (wB X (D.naut.plGw kv.1 kv.2)) :=
  scal_of_vec X kv (sub_mem (one_mem _) X.ew_int) (hE X.z0 X.vectorsInLattice.2.1)

/- English proof (translation)
Establish `hp` using `D.host.g_prime kv.1`. Establish `hcard : Nat.card (𝓞 X.B.I.E ⧸ (wB X (D.naut.plGw kv.1 kv.2)).asIdeal) = D.host.g kv.1`. Rewrite using `[card_wB, card_res_host]`. Establish `hn : 0 < X.B.I.n` using `by rw [X.n_eq, r_eq]; omega`. Use `haveI : Fact (D.host.g kv.1).Prime := ⟨hp⟩`.

Take `⟨m, hm⟩` from `congW_exists hp hcard X.ew_int`. Establish `hmm` using `congW_mul X.ew_int hm hm`. Rewrite `hmm` using `[X.ew_idem]`. Establish `hm2 : m = m * m` using `congW_unique hp hcard hn hm hmm`. Establish `h01 : m = 0 ∨ m = 1`.

Establish `: m * (m - 1) = 0` using `by rw [mul_sub, mul_one, ← hm2, sub_self]`. Break down `mul_eq_zero.1 this with h | h` into its components or cases. Conclude with `Or.inl h`. Conclude with `Or.inr (sub_eq_zero.1 h)`. Break down `h01 with rfl | rfl` into its components or cases.

Establish `hew : X.ew ∈ Wq X.B.I (wB X (D.naut.plGw kv.1 kv.2))`. Use `congW_eq_mem hp hcard hm (congW_zero_of (zero_mem _))` as an intermediate fact. Simplify using `using this`. Establish `hint : 1 - X.ew - sg X.B.I X.ew ∈ IntAf X.B.I.F X.B.I.E` using `sub_mem (sub_mem (one_mem _) X.ew_int) (DictLat.sigR_int X.B.I X.ew_int)`. Establish `hfull` using `scal_of_vec X kv hint (mL_le X kv (X.ew_full _ X.vectorsInLattice.2.1))`.

Establish `e : 1 - sg X.B.I X.ew = (1 - X.ew - sg X.B.I X.ew) + X.ew` using `by ring`. Rewrite using `[e]`. Conclude with `add_mem hfull hew`. It suffices to derive a contradiction. Apply `hE` to reduce the goal to its premises.

Introduce `y hy`. Establish `h1 : X.ew - 1 ∈ Wq X.B.I (wB X (D.naut.plGw kv.1 kv.2))` using `congW_eq_mem hp hcard hm ⟨1, by simp, by simp⟩`. Establish `h2 : 1 - X.ew ∈ Wq X.B.I (wB X (D.naut.plGw kv.1 kv.2))`. Rewrite using `[← neg_sub]`. Conclude with `neg_mem h1`.

Rewrite using `[wLf_eq]`. Conclude with `Wq_smul h2 hy`.
-/
theorem ew_not (X : HidaSetting D) (kv : Σ k : Fin 2, D.nd.PlG k)
    (hE : ¬ GlobalTheory.Mem.SymFrame.EwAt X (D.naut.plGw kv.1 kv.2)) :
    1 - sg X.B.I X.ew ∈ Wq X.B.I (wB X (D.naut.plGw kv.1 kv.2)) := by
  have hp := D.host.g_prime kv.1
  have hcard : Nat.card (𝓞 X.B.I.E ⧸ (wB X (D.naut.plGw kv.1 kv.2)).asIdeal) = D.host.g kv.1 := by
    rw [card_wB, card_res_host]
  have hn : 0 < X.B.I.n := by rw [X.n_eq, r_eq]; omega
  haveI : Fact (D.host.g kv.1).Prime := ⟨hp⟩
  obtain ⟨m, hm⟩ := congW_exists hp hcard X.ew_int
  have hmm := congW_mul X.ew_int hm hm
  rw [X.ew_idem] at hmm
  have hm2 : m = m * m := congW_unique hp hcard hn hm hmm
  have h01 : m = 0 ∨ m = 1 := by
    have : m * (m - 1) = 0 := by rw [mul_sub, mul_one, ← hm2, sub_self]
    rcases mul_eq_zero.1 this with h | h
    · exact Or.inl h
    · exact Or.inr (sub_eq_zero.1 h)
  rcases h01 with rfl | rfl
  · have hew : X.ew ∈ Wq X.B.I (wB X (D.naut.plGw kv.1 kv.2)) := by
      have := congW_eq_mem hp hcard hm (congW_zero_of (zero_mem _))
      simpa using this
    have hint : 1 - X.ew - sg X.B.I X.ew ∈ IntAf X.B.I.F X.B.I.E :=
      sub_mem (sub_mem (one_mem _) X.ew_int) (DictLat.sigR_int X.B.I X.ew_int)
    have hfull := scal_of_vec X kv hint (mL_le X kv (X.ew_full _ X.vectorsInLattice.2.1))
    have e : 1 - sg X.B.I X.ew = (1 - X.ew - sg X.B.I X.ew) + X.ew := by ring
    rw [e]
    exact add_mem hfull hew
  · exfalso
    apply hE
    intro y hy
    have h1 : X.ew - 1 ∈ Wq X.B.I (wB X (D.naut.plGw kv.1 kv.2)) :=
      congW_eq_mem hp hcard hm ⟨1, by simp, by simp⟩
    have h2 : 1 - X.ew ∈ Wq X.B.I (wB X (D.naut.plGw kv.1 kv.2)) := by
      rw [← neg_sub]; exact neg_mem h1
    rw [wLf_eq]
    exact Wq_smul h2 hy

end GlobalTheory.Mem.SymFrameRed

namespace GlobalTheory.Mem.SymFrameRed

open Formalism.MainNotions.S Formalism.L2.SG.Pf.RowDictPf PIW.AdelClassFin Formalism.L2.SG.Pf.RedBasicsPf Formalism.L2.SG.Pf.unitaryCongruence
  Formalism.L2.SG.Pf.AllRowsRedKerA Formalism.L2.SG.Pf.KppRedW Formalism.L2.SG.Pf.AllRowsRho Formalism.L2.SG.Pf.KppFrameW

variable {D : D7}

open Classical in

def epsD (X : HidaSetting D) (w : HeightOneSpectrum (𝓞 D.host.E)) : Fin D.R.k → VA X.B.I :=
  if GlobalTheory.Mem.SymFrame.EwAt X w then X.bwd else fun i => X.bw (Fin.rev i)

/- English proof (translation)
Establish `hp` using `D.host.g_prime kv.1`. Establish `hcard : Nat.card (𝓞 X.B.I.E ⧸ (wB X (D.naut.plGw kv.1 kv.2)).asIdeal) = D.host.g kv.1`. Rewrite using `[card_wB, card_res_host]`. Use `haveI : NeZero (D.host.g kv.1) := ⟨hp.ne_zero⟩`. Establish `hm : D.R.r = X.B.I.n` using `X.n_eq.symm`.

Establish `hb0 : IsRedBasis0 X.B.I (wB X (D.naut.plGw kv.1 kv.2)) b`. Establish `h` using `hb`. Unfold `IsRedBasis at h`. Rewrite `h` using `[wLat_eq]`. Conclude with `h`.

Establish `fam : ∀ x, ((∃ i, x = X.bw i) ∨ (∃ i, x = X.bwd i)) → ZMod' X.B.I X.B.g (hA X.B.I X.z0 x) ∧ ∀ a, ZMod' X.B.I X.B.g (hA X.B.I (X.e0 a) x) ∧ ZMod' X.B.I X.B.g (hA X.B.I (X.f0 a) x)`. Introduce and unpack `x (⟨i, rfl⟩ | ⟨i, rfl⟩)`. Conclude with `⟨(X.weightVectorsIntegral i).1, fun a => ⟨((X.weightVectorsIntegral i).2.2 a).1, ((X.weightVectorsIntegral i).2.2 a).2.1⟩⟩`. Conclude with `⟨(X.weightVectorsIntegral i).2.1, fun a => ⟨((X.weightVectorsIntegral i).2.2 a).2.2.1, ((X.weightVectorsIntegral i).2.2 a).2.2.2⟩⟩`. Establish `hε : ∀ j, (∃ i, GlobalTheory.Mem.SymFrame.epsW X (D.naut.plGw kv.1 kv.2) j = X.bw i) ∨ (∃ i, GlobalTheory.Mem.SymFrame.epsW X (D.naut.plGw kv.1 kv.2) j = X.bwd i)`.

Introduce `j`. Unfold `GlobalTheory.Mem.SymFrame.epsW`. Use `split_ifs`. Conclude with `Or.inl ⟨j, rfl⟩`. Conclude with `Or.inr ⟨_, rfl⟩`.

Establish `hεd : ∀ j, (∃ i, epsD X (D.naut.plGw kv.1 kv.2) j = X.bw i) ∨ (∃ i, epsD X (D.naut.plGw kv.1 kv.2) j = X.bwd i)`. Introduce `j`. Unfold `epsD`. Use `split_ifs`. Conclude with `Or.inr ⟨j, rfl⟩`.

Conclude with `Or.inl ⟨_, rfl⟩`. Establish `hbb : ∀ i j, hhat X.B.I (epsD X (D.naut.plGw kv.1 kv.2) i) (GlobalTheory.Mem.SymFrame.epsW X (D.naut.plGw kv.1 kv.2) j) - (if i = j then 1 else 0) ∈ Wq X.B.I (wB X (D.naut.plGw kv.1 kv.2))`. Introduce `i j`. Distinguish the cases in `hE : GlobalTheory.Mem.SymFrame.EwAt X (D.naut.plGw kv.1 kv.2)`. Simplify using `only [epsD, GlobalTheory.Mem.SymFrame.epsW, if_pos hE]`.

Establish `h1` using `zmod_Wq X kv (X.bw_dual i j)`. Establish `h2 : (if i = j then X.ew - 1 else 0) ∈ Wq X.B.I (wB X (D.naut.plGw kv.1 kv.2))` using `by split_ifs`. Rewrite using `[← neg_sub]`. Conclude with `neg_mem (ew_at X kv hE)`. Conclude with `zero_mem _`.

Apply the tactic sequence `have e : hhat X.B.I (X.bwd i) (X.bw j) - (if i = j then 1 else 0) = (hA X.B.I (X.bwd i) (X.bw j) - if i = j then X.ew else 0) + (if i = j then X.ew - 1 else 0) := by show _ = (hhat X.B.I (X.bwd i) (X.bw j) - if i = j then X.ew else 0) + (if i = j then X.ew - 1 else 0) split_ifs < …`. Rewrite using `[e]`. Conclude with `add_mem h1 h2`. Simplify using `only [epsD, GlobalTheory.Mem.SymFrame.epsW, if_neg hE]`. Establish `h1` using `sw X kv (X.bw_dual (Fin.rev j) (Fin.rev i))`.

Establish `h2 : (if i = j then sg X.B.I X.ew - 1 else 0) ∈ Wq X.B.I (wB X (D.naut.plGw kv.1 kv.2))` using `by split_ifs`. Rewrite using `[← neg_sub]`. Conclude with `neg_mem (ew_not X kv hE)`. Conclude with `zero_mem _`. Establish `e : hhat X.B.I (X.bw (Fin.rev i)) (X.bwd (Fin.rev j)) - (if i = j then 1 else 0) = (hhat X.B.I (X.bw (Fin.rev i)) (X.bwd (Fin.rev j)) - sg X.B.I (if Fin.rev j = Fin.rev i then X.ew else 0)) + (if i = j then sg X.B.I X.ew - 1 else 0)`.

Distinguish the cases in `h : i = j`. Substitute `h` using the available equality. Simplify using `only [if_true]`. Expand and normalize the polynomial expressions, which then agree. Establish `h' : ¬ Fin.rev j = Fin.rev i` using `fun h' => h (Fin.rev_injective h').symm`.

Simplify using `only [h, h', if_false, map_zero, sub_zero, add_zero]`. Rewrite using `[e]`. Conclude with `add_mem h1 h2`. Set `fr : Fin D.R.r → VA X.B.I` to `fun j => GlobalTheory.Mem.SymFrame.symVec X (D.naut.plGw kv.1 kv.2) (π.symm j)`. Set `frd : Fin D.R.r → VA X.B.I` to `fun i => GlobalTheory.SeeConjRead.flagV D.R.rS D.R.k D.R.r X.f0 X.e0 (epsD X (D.naut.plGw kv.1 kv.2)) (-X.z0) (π.symm i)`.

Establish `hbwL : ∀ x, ((∃ i, x = X.bw i) ∨ (∃ i, x = X.bwd i)) → x ∈ X.B.I.Lf`. Introduce and unpack `x (⟨i, rfl⟩ | ⟨i, rfl⟩)`. Conclude with `(X.vectorsInLattice.2.2 i).1`. Conclude with `(X.vectorsInLattice.2.2 i).2`. Establish `hfr : ∀ j, fr j ∈ X.B.I.Lf` using `fun j => flagV_mem (· ∈ X.B.I.Lf) (zero_mem _) (fun a => (X.vectorsInLattice.1 a).1) (fun a => (X.vectorsInLattice.1 a).2) (fun i => hbwL _ (hε i)) X.vectorsInLattice.2.1 _`.

Establish `hfrd : ∀ i, frd i ∈ X.B.I.Lf` using `fun j => flagV_mem (· ∈ X.B.I.Lf) (zero_mem _) (fun a => (X.vectorsInLattice.1 a).2) (fun a => (X.vectorsInLattice.1 a).1) (fun i => hbwL _ (hεd i)) (neg_mem X.vectorsInLattice.2.1) _`. Establish `hG : GramW (wB X (D.naut.plGw kv.1 kv.2)) fr frd`. Introduce `i j`. Use `gram_flagV (Wq X.B.I (wB X (D.naut.plGw kv.1 kv.2))).toAddSubgroup (hhat X.B.I) (r_eq D) X.e0 X.f0 X.f0 X.e0 (GlobalTheory.Mem.SymFrame.epsW X (D.naut.plGw kv.1 kv.2)) (epsD X (D.naut.plGw kv.1 kv.2)) X.z0 (-X.z0) (fun a c => by` as an intermediate fact. Establish `h` using `sw X kv (X.gramIntegral c a).2.2`.

Rewrite `h` using `[sg_ite, map_one]`. Simplify `h)` using `only [@eq_comm _ c a, Submodule.mem_toAddSubgroup]`. Use the proof step `(fun a j => zmod_Wq X kv ((fam _ (hε j)).2 a).2)`. Use the proof step `(fun a => zmod_Wq X kv ((X.formsAtZero.2 a).2))`. Use the proof step `(fun a c => zmod_Wq X kv (X.gramIntegral a c).2.1)`.

Use the proof step `(fun i c => sw0 X kv ((fam _ (hεd i)).2 c).1)`. Use `hbb`. Use the proof step `(fun i => sw0 X kv (fam _ (hεd i)).1)`. Use the proof step `(fun i c => sw0 X kv ((fam _ (hεd i)).2 c).2)`. Use the proof step `(fun c => by show hhat X.B.I (-X.z0) (X.e0 c) ∈ _`.

Rewrite using `[hhat_neg]`. Conclude with `neg_mem (sw0 X kv (X.formsAtZero.2 c).1))`. Use the proof step `(fun j => by show hhat X.B.I (-X.z0) _ ∈ _`. Rewrite using `[hhat_neg]`. Conclude with `neg_mem (zmod_Wq X kv (fam _ (hε j)).1))`.

Use the proof step `(by show hhat X.B.I (-X.z0) X.z0 - 1 ∈ _`. Rewrite using `[hhat_neg, show -hhat X.B.I X.z0 X.z0 - 1 = -(hhat X.B.I X.z0 X.z0 + 1) by ring]`. Conclude with `neg_mem (zmod_Wq X kv X.formsAtZero.1))`. Use the proof step `(fun c => by show hhat X.B.I (-X.z0) (X.f0 c) ∈ _`. Rewrite using `[hhat_neg]`.

Conclude with `neg_mem (sw0 X kv (X.formsAtZero.2 c).2))`. Use the proof step `(fun a c => zmod_Wq X kv (X.gramIntegral a c).1)`. Use the proof step `(fun a j => zmod_Wq X kv ((fam _ (hε j)).2 a).1)`. Use the proof step `(fun a => zmod_Wq X kv ((X.formsAtZero.2 a).1))`. Use the proof step `(fun a c => zmod_Wq X kv (X.gramIntegral a c).2.2)`.

Use the proof step `(π.symm i) (π.symm j)`. Simplify using `only [Equiv.apply_eq_iff_eq, Submodule.mem_toAddSubgroup] at this`. Conclude with `this`. Take `⟨c, hc⟩` from `exists_lifts hp hcard hfr`. Establish `hcL : ∀ j, c j ∈ X.B.I.L` using `fun j => (hc j).1`.

Establish `hcq : ∀ j, fr j - iv X.B.I (c j) ∈ Lq X.B.I (wB X (D.naut.plGw kv.1 kv.2))` using `fun j => (hc j).2`. Establish `hG'` using `gram_lift hfrd hG hcq`. Establish `hcB : IsRedBasis0 X.B.I (wB X (D.naut.plGw kv.1 kv.2)) c` using `isRedBasis_of_gram hp hcard hm hfrd hcL hG'`. Use `choose Pc hPc using fun j => rep_exists hp hcard hb0 (hfr j)`. Use `choose Qc hQc using fun j => rep_exists hp hcard hcB (DictLat.iv_mem X.B.I (hb0.1 j))`.

Set `P : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1))` to `Matrix.of fun k j => Pc j k`. Set `Q : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1))` to `Matrix.of fun k j => Qc j k`. Establish `hP : ∀ j, RepV (wB X (D.naut.plGw kv.1 kv.2)) (D.host.g kv.1) (fun k => iv X.B.I (b k)) (iv X.B.I (c j)) (fun k => P k j)`. Introduce `j`. Establish `h1` using `hPc j`.

Unfold `RepV at h1 ⊢`. Use `sub_mem h1 (hcq j)` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Simplify using `only [P, Matrix.of_apply]`. Normalize the expressions using the abelian group laws.

Establish `hQ : ∀ j, RepV (wB X (D.naut.plGw kv.1 kv.2)) (D.host.g kv.1) (fun k => iv X.B.I (c k)) (iv X.B.I (b j)) (fun k => Q k j)` using `hQc`. Establish `hPQ : P * Q = 1`. Use extensionality with `i j`. Establish `h1` using `rep_comp hp hcard hb0.1 (hQ j) hP`. Establish `h2` using `rep_self (w := wB X (D.naut.plGw kv.1 kv.2)) hp (fun k => iv X.B.I (b k)) j`.

Use `rep_unique hp hcard hm hb0 h1 h2` as an intermediate fact. Use `congrFun this i` as an intermediate fact. Simplify `this` using `[Matrix.mulVec, dotProduct, Matrix.mul_apply]`. Establish `hQP : Q * P = 1` using `(Matrix.mul_eq_one_comm_of_card_eq (Fin D.R.r) (Fin D.R.r) _ rfl).mp hPQ`. Use `⟨⟨P, Q, hPQ, hQP⟩, fun j => ?_⟩` and prove the remaining obligations.

Rewrite using `[wLf_eq]`. Conclude with `hPc j`.
-/
theorem main_kv (X : HidaSetting D) (b : Fin D.R.r → Fin X.B.I.n → X.B.I.E) (kv : Σ k : Fin 2, D.nd.PlG k)
    (hb : IsRedBasis X (D.naut.plGw kv.1 kv.2) b) (π : Equiv.Perm (Fin D.R.r)) :
    ∃ P : GL (Fin D.R.r) (ZMod (D.host.g kv.1)), ∀ j,
      GlobalTheory.Mem.SymFrame.symVec X (D.naut.plGw kv.1 kv.2) (π.symm j) -
        ∑ i, ((((P : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1))) i j).val : ℕ) :
          X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • incl X.B.I (b i) ∈ wLf X (D.naut.plGw kv.1 kv.2) := by
  have hp := D.host.g_prime kv.1
  have hcard : Nat.card (𝓞 X.B.I.E ⧸ (wB X (D.naut.plGw kv.1 kv.2)).asIdeal) = D.host.g kv.1 := by
    rw [card_wB, card_res_host]
  haveI : NeZero (D.host.g kv.1) := ⟨hp.ne_zero⟩
  have hm : D.R.r = X.B.I.n := X.n_eq.symm
  have hb0 : IsRedBasis0 X.B.I (wB X (D.naut.plGw kv.1 kv.2)) b := by
    have h := hb
    unfold IsRedBasis at h
    rw [wLat_eq] at h
    exact h

  have fam : ∀ x, ((∃ i, x = X.bw i) ∨ (∃ i, x = X.bwd i)) → ZMod' X.B.I X.B.g (hA X.B.I X.z0 x) ∧
      ∀ a, ZMod' X.B.I X.B.g (hA X.B.I (X.e0 a) x) ∧ ZMod' X.B.I X.B.g (hA X.B.I (X.f0 a) x) := by
    rintro x (⟨i, rfl⟩ | ⟨i, rfl⟩)
    · exact ⟨(X.weightVectorsIntegral i).1, fun a => ⟨((X.weightVectorsIntegral i).2.2 a).1, ((X.weightVectorsIntegral i).2.2 a).2.1⟩⟩
    · exact ⟨(X.weightVectorsIntegral i).2.1, fun a => ⟨((X.weightVectorsIntegral i).2.2 a).2.2.1, ((X.weightVectorsIntegral i).2.2 a).2.2.2⟩⟩
  have hε : ∀ j, (∃ i, GlobalTheory.Mem.SymFrame.epsW X (D.naut.plGw kv.1 kv.2) j = X.bw i) ∨
      (∃ i, GlobalTheory.Mem.SymFrame.epsW X (D.naut.plGw kv.1 kv.2) j = X.bwd i) := by
    intro j
    unfold GlobalTheory.Mem.SymFrame.epsW
    split_ifs
    · exact Or.inl ⟨j, rfl⟩
    · exact Or.inr ⟨_, rfl⟩
  have hεd : ∀ j, (∃ i, epsD X (D.naut.plGw kv.1 kv.2) j = X.bw i) ∨
      (∃ i, epsD X (D.naut.plGw kv.1 kv.2) j = X.bwd i) := by
    intro j
    unfold epsD
    split_ifs
    · exact Or.inr ⟨j, rfl⟩
    · exact Or.inl ⟨_, rfl⟩
  have hbb : ∀ i j, hhat X.B.I (epsD X (D.naut.plGw kv.1 kv.2) i) (GlobalTheory.Mem.SymFrame.epsW X (D.naut.plGw kv.1 kv.2) j) -
      (if i = j then 1 else 0) ∈ Wq X.B.I (wB X (D.naut.plGw kv.1 kv.2)) := by
    intro i j
    by_cases hE : GlobalTheory.Mem.SymFrame.EwAt X (D.naut.plGw kv.1 kv.2)
    · simp only [epsD, GlobalTheory.Mem.SymFrame.epsW, if_pos hE]
      have h1 := zmod_Wq X kv (X.bw_dual i j)
      have h2 : (if i = j then X.ew - 1 else 0) ∈ Wq X.B.I (wB X (D.naut.plGw kv.1 kv.2)) := by
        split_ifs
        · rw [← neg_sub]; exact neg_mem (ew_at X kv hE)
        · exact zero_mem _
      have e : hhat X.B.I (X.bwd i) (X.bw j) - (if i = j then 1 else 0) =
          (hA X.B.I (X.bwd i) (X.bw j) - if i = j then X.ew else 0) + (if i = j then X.ew - 1 else 0) := by
        show _ = (hhat X.B.I (X.bwd i) (X.bw j) - if i = j then X.ew else 0) + (if i = j then X.ew - 1 else 0)
        split_ifs <;> ring
      rw [e]
      exact add_mem h1 h2
    · simp only [epsD, GlobalTheory.Mem.SymFrame.epsW, if_neg hE]
      have h1 := sw X kv (X.bw_dual (Fin.rev j) (Fin.rev i))
      have h2 : (if i = j then sg X.B.I X.ew - 1 else 0) ∈ Wq X.B.I (wB X (D.naut.plGw kv.1 kv.2)) := by
        split_ifs
        · rw [← neg_sub]; exact neg_mem (ew_not X kv hE)
        · exact zero_mem _
      have e : hhat X.B.I (X.bw (Fin.rev i)) (X.bwd (Fin.rev j)) - (if i = j then 1 else 0) =
          (hhat X.B.I (X.bw (Fin.rev i)) (X.bwd (Fin.rev j)) -
            sg X.B.I (if Fin.rev j = Fin.rev i then X.ew else 0)) + (if i = j then sg X.B.I X.ew - 1 else 0) := by
        by_cases h : i = j
        · subst h; simp only [if_true]; ring
        · have h' : ¬ Fin.rev j = Fin.rev i := fun h' => h (Fin.rev_injective h').symm
          simp only [h, h', if_false, map_zero, sub_zero, add_zero]
      rw [e]
      exact add_mem h1 h2

  let fr : Fin D.R.r → VA X.B.I := fun j => GlobalTheory.Mem.SymFrame.symVec X (D.naut.plGw kv.1 kv.2) (π.symm j)
  let frd : Fin D.R.r → VA X.B.I := fun i =>
    GlobalTheory.SeeConjRead.flagV D.R.rS D.R.k D.R.r X.f0 X.e0 (epsD X (D.naut.plGw kv.1 kv.2)) (-X.z0) (π.symm i)
  have hbwL : ∀ x, ((∃ i, x = X.bw i) ∨ (∃ i, x = X.bwd i)) → x ∈ X.B.I.Lf := by
    rintro x (⟨i, rfl⟩ | ⟨i, rfl⟩)
    · exact (X.vectorsInLattice.2.2 i).1
    · exact (X.vectorsInLattice.2.2 i).2
  have hfr : ∀ j, fr j ∈ X.B.I.Lf := fun j =>
    flagV_mem (· ∈ X.B.I.Lf) (zero_mem _) (fun a => (X.vectorsInLattice.1 a).1) (fun a => (X.vectorsInLattice.1 a).2)
      (fun i => hbwL _ (hε i)) X.vectorsInLattice.2.1 _
  have hfrd : ∀ i, frd i ∈ X.B.I.Lf := fun j =>
    flagV_mem (· ∈ X.B.I.Lf) (zero_mem _) (fun a => (X.vectorsInLattice.1 a).2) (fun a => (X.vectorsInLattice.1 a).1)
      (fun i => hbwL _ (hεd i)) (neg_mem X.vectorsInLattice.2.1) _
  have hG : GramW (wB X (D.naut.plGw kv.1 kv.2)) fr frd := by
    intro i j
    have := gram_flagV (Wq X.B.I (wB X (D.naut.plGw kv.1 kv.2))).toAddSubgroup (hhat X.B.I) (r_eq D)
      X.e0 X.f0 X.f0 X.e0 (GlobalTheory.Mem.SymFrame.epsW X (D.naut.plGw kv.1 kv.2)) (epsD X (D.naut.plGw kv.1 kv.2))
      X.z0 (-X.z0)
      (fun a c => by
        have h := sw X kv (X.gramIntegral c a).2.2
        rw [sg_ite, map_one] at h
        simpa only [@eq_comm _ c a, Submodule.mem_toAddSubgroup] using h)
      (fun a j => zmod_Wq X kv ((fam _ (hε j)).2 a).2)
      (fun a => zmod_Wq X kv ((X.formsAtZero.2 a).2))
      (fun a c => zmod_Wq X kv (X.gramIntegral a c).2.1)
      (fun i c => sw0 X kv ((fam _ (hεd i)).2 c).1)
      hbb
      (fun i => sw0 X kv (fam _ (hεd i)).1)
      (fun i c => sw0 X kv ((fam _ (hεd i)).2 c).2)
      (fun c => by
        show hhat X.B.I (-X.z0) (X.e0 c) ∈ _
        rw [hhat_neg]; exact neg_mem (sw0 X kv (X.formsAtZero.2 c).1))
      (fun j => by
        show hhat X.B.I (-X.z0) _ ∈ _
        rw [hhat_neg]; exact neg_mem (zmod_Wq X kv (fam _ (hε j)).1))
      (by
        show hhat X.B.I (-X.z0) X.z0 - 1 ∈ _
        rw [hhat_neg, show -hhat X.B.I X.z0 X.z0 - 1 = -(hhat X.B.I X.z0 X.z0 + 1) by ring]
        exact neg_mem (zmod_Wq X kv X.formsAtZero.1))
      (fun c => by
        show hhat X.B.I (-X.z0) (X.f0 c) ∈ _
        rw [hhat_neg]; exact neg_mem (sw0 X kv (X.formsAtZero.2 c).2))
      (fun a c => zmod_Wq X kv (X.gramIntegral a c).1)
      (fun a j => zmod_Wq X kv ((fam _ (hε j)).2 a).1)
      (fun a => zmod_Wq X kv ((X.formsAtZero.2 a).1))
      (fun a c => zmod_Wq X kv (X.gramIntegral a c).2.2)
      (π.symm i) (π.symm j)
    simp only [Equiv.apply_eq_iff_eq, Submodule.mem_toAddSubgroup] at this
    exact this
  obtain ⟨c, hc⟩ := exists_lifts hp hcard hfr
  have hcL : ∀ j, c j ∈ X.B.I.L := fun j => (hc j).1
  have hcq : ∀ j, fr j - iv X.B.I (c j) ∈ Lq X.B.I (wB X (D.naut.plGw kv.1 kv.2)) := fun j => (hc j).2
  have hG' := gram_lift hfrd hG hcq
  have hcB : IsRedBasis0 X.B.I (wB X (D.naut.plGw kv.1 kv.2)) c := isRedBasis_of_gram hp hcard hm hfrd hcL hG'
  choose Pc hPc using fun j => rep_exists hp hcard hb0 (hfr j)
  choose Qc hQc using fun j => rep_exists hp hcard hcB (DictLat.iv_mem X.B.I (hb0.1 j))
  let P : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1)) := Matrix.of fun k j => Pc j k
  let Q : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1)) := Matrix.of fun k j => Qc j k
  have hP : ∀ j, RepV (wB X (D.naut.plGw kv.1 kv.2)) (D.host.g kv.1) (fun k => iv X.B.I (b k)) (iv X.B.I (c j))
      (fun k => P k j) := by
    intro j
    have h1 := hPc j
    unfold RepV at h1 ⊢
    have := sub_mem h1 (hcq j)
    convert this using 1
    simp only [P, Matrix.of_apply]
    abel
  have hQ : ∀ j, RepV (wB X (D.naut.plGw kv.1 kv.2)) (D.host.g kv.1) (fun k => iv X.B.I (c k)) (iv X.B.I (b j))
      (fun k => Q k j) := hQc
  have hPQ : P * Q = 1 := by
    ext i j
    have h1 := rep_comp hp hcard hb0.1 (hQ j) hP
    have h2 := rep_self (w := wB X (D.naut.plGw kv.1 kv.2)) hp (fun k => iv X.B.I (b k)) j
    have := rep_unique hp hcard hm hb0 h1 h2
    have := congrFun this i
    simpa [Matrix.mulVec, dotProduct, Matrix.mul_apply] using this
  have hQP : Q * P = 1 := (Matrix.mul_eq_one_comm_of_card_eq (Fin D.R.r) (Fin D.R.r) _ rfl).mp hPQ
  refine ⟨⟨P, Q, hPQ, hQP⟩, fun j => ?_⟩
  rw [wLf_eq]
  exact hPc j

/- English proof (translation)
Introduce `D X _ _ b hb _ π`. Use `choose P hP using fun kv => main_kv X (b kv) kv (hb kv) π`. Conclude with `⟨P, fun kv j => hP kv j⟩`.
-/
theorem symVec_red : ∀ (D : D7) (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), (∀ x : X.B.I.E, HEq (X.ιE x) x) → ∀ (b : (Σ k : Fin 2, D.nd.PlG k) → Fin D.R.r → Fin X.B.I.n → X.B.I.E), (∀ kv : (Σ k : Fin 2, D.nd.PlG k), IsRedBasis X (D.naut.plGw kv.1 kv.2) (b kv)) → (∀ kv : (Σ k : Fin 2, D.nd.PlG k), ((D.host.g kv.1 : ℕ) : 𝓞 D.host.E) ∈ (D.naut.plGw kv.1 kv.2).asIdeal) → ∀ π : Equiv.Perm (Fin D.R.r), ∃ P : G0g D.nd, ∀ (kv : (Σ k : Fin 2, D.nd.PlG k)) (j : Fin D.R.r), GlobalTheory.Mem.SymFrame.symVec X (D.naut.plGw kv.1 kv.2) (π.symm j) - ∑ i, ((((((P kv : GL (Fin D.R.r) (ZMod (D.host.g kv.1))) : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1)))) i j).val : ℕ) : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) • incl X.B.I (b kv i) ∈ wLf X (D.naut.plGw kv.1 kv.2) := by
  intro D X _ _ b hb _ π
  choose P hP using fun kv => main_kv X (b kv) kv (hb kv) π
  exact ⟨P, fun kv j => hP kv j⟩

end GlobalTheory.Mem.SymFrameRed
