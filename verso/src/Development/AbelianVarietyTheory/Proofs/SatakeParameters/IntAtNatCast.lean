import Mathlib
import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth

open NumberField IsDedekindDomain Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.BasicNotions Formalism.L2.DIV

namespace GlobalTheory.GO.ChRoot

section Loc

variable {E : Type} [Field E] [NumberField E] {P : HeightOneSpectrum (𝓞 E)}

/- English proof (translation)
Simplify using `using IntAt.coe P (k : 𝓞 E)`.
-/
theorem intAt_natCast (k : ℕ) : IntAt P (k : E) := by simpa using IntAt.coe P (k : 𝓞 E)

/- English proof (translation)
Simplify using `using intAt_natCast (P := P) 0`.
-/
theorem intAt_zero' : IntAt P (0 : E) := by simpa using intAt_natCast (P := P) 0

/- English proof (translation)
Simplify using `using intAt_natCast (P := P) 1`.
-/
theorem intAt_one' : IntAt P (1 : E) := by simpa using intAt_natCast (P := P) 1

/- English proof (translation)
The claim follows from `Nat.pos_of_ne_zero fun h => P.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)`.
-/
theorem qOf_pos (P : HeightOneSpectrum (𝓞 E)) : 0 < qOf P :=
  Nat.pos_of_ne_zero fun h => P.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)

variable [StarRing E]

/- English proof (translation)
The claim follows from `mem_localization_standardLattice P x`.
-/
theorem mem_stdAt' {n : ℕ} {x : Sp E n} : x ∈ stdAt E n P ↔ ∀ i, IntAt P (x i) := mem_localization_standardLattice P x

/- English proof (translation)
Unfold `LocE.lamY LocE.sclLat`. Rewrite using `[Submodule.mem_comap, mem_stdAt', mem_stdAt']`. Use `forall_congr' fun i => ?_` and prove the remaining obligations. Simplify using `[LocE.scE]`.
-/
theorem mem_lamY_zero {q n c : ℕ} {x : Sp E (n + c)} : x ∈ LocE.lamY P q n c 0 ↔ x ∈ stdAt E (n + c) P := by
  unfold LocE.lamY LocE.sclLat
  rw [Submodule.mem_comap, mem_stdAt', mem_stdAt']
  refine forall_congr' fun i => ?_
  simp [LocE.scE]

/- English proof (translation)
Rewrite using `[mem_stdAt']`. Introduce `l`. Unfold `Loc.eN`. Use `split_ifs`. Conclude with `intAt_one'`.

Conclude with `intAt_zero'`.
-/
theorem eN_mem {N i : ℕ} : Loc.eN E N i ∈ stdAt E N P := by
  rw [mem_stdAt']
  intro l
  unfold Loc.eN
  split_ifs
  · exact intAt_one'
  · exact intAt_zero'

/- English proof (translation)
Unfold `Loc.n1Arg`. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_induction _ (IntAt P) (fun _ _ ha hb => ha.add hb) intAt_zero' fun i _ => ?_` and prove the remaining obligations. Unfold `Loc.atN`. Use `split_ifs with hi`.

Conclude with `mem_stdAt'.1 (h _ eN_mem) ⟨n + i, hi⟩`. Simplify using `using intAt_zero'`.
-/
theorem intAt_n1Arg {n c : ℕ} (a : E) (r : Sp E (n + c) ≃ₗ[E] Sp E (n + c))
    (h : ∀ x ∈ stdAt E (n + c) P, a • r x ∈ stdAt E (n + c) P) : IntAt P (a * Loc.n1Arg r) := by
  unfold Loc.n1Arg
  rw [Finset.mul_sum]
  refine Finset.sum_induction _ (IntAt P) (fun _ _ ha hb => ha.add hb) intAt_zero' fun i _ => ?_
  unfold Loc.atN
  split_ifs with hi
  · exact mem_stdAt'.1 (h _ eN_mem) ⟨n + i, hi⟩
  · simpa using intAt_zero'

omit [StarRing E] in

/- English proof (translation)
Unfold `LocE.unitV at h ⊢`. Use `split_ifs at h ⊢ with hu`. Establish `: Finite (𝓞 E ⧸ P.asIdeal)` using `Ideal.finiteQuotientOfFreeOfNeBot _ P.ne_bot`. Use `⟨Nat.card (𝓞 E ⧸ P.asIdeal)ˣ, Nat.card_pos, ?_⟩` and prove the remaining obligations. Rewrite using `[← Units.val_pow_eq_pow_val, ← map_pow, pow_card_eq_one', map_one, Units.val_one]`.

Conclude with `absurd rfl h`.
-/
theorem unitV_root {K : Type} [Field K] (χ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) (a : E) (h : LocE.unitV χ a ≠ 0) :
    ∃ k : ℕ, 0 < k ∧ LocE.unitV χ a ^ k = 1 := by
  unfold LocE.unitV at h ⊢
  split_ifs at h ⊢ with hu
  · have : Finite (𝓞 E ⧸ P.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ P.ne_bot
    refine ⟨Nat.card (𝓞 E ⧸ P.asIdeal)ˣ, Nat.card_pos, ?_⟩
    rw [← Units.val_pow_eq_pow_val, ← map_pow, pow_card_eq_one', map_one, Units.val_one]
  · exact absurd rfl h

end Loc

/- English proof (translation)
Establish `key : ∀ k : ℕ, c.psi P ((k : X.E) * x) = c.psi P x ^ k`. Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => simpa using hc.psi_int P 0 intAt_zero'`. Consider the case `succ k ih`.

Rewrite using `[Nat.cast_succ, add_mul, one_mul, hc.psi_add P _ _ _ hx, ih, pow_succ]`. Rewrite using `[mul_left_comm]`. Conclude with `(intAt_natCast k).mul hx`. Rewrite using `[← key]`. Conclude with `hc.psi_int P _ (by simpa using hx)`.
-/
theorem psi_root {X : Fields} {SB : Finset (HeightOneSpectrum (𝓞 X.E))} {c : LocCst X SB} (hc : c.Ok) (P : SB) (x : X.E)
    (hx : IntAt P.1 ((qOf P.1 : X.E) ^ c.D P * x)) : c.psi P x ^ (qOf P.1 ^ c.D P) = 1 := by
  have key : ∀ k : ℕ, c.psi P ((k : X.E) * x) = c.psi P x ^ k := by
    intro k
    induction k with
    | zero => simpa using hc.psi_int P 0 intAt_zero'
    | succ k ih =>
      rw [Nat.cast_succ, add_mul, one_mul, hc.psi_add P _ _ _ hx, ih, pow_succ]
      rw [mul_left_comm]
      exact (intAt_natCast k).mul hx
  rw [← key]
  exact hc.psi_int P _ (by simpa using hx)

/- English proof (translation)
Establish `hg` using `Subgroup.mem_subgroupOf.1 ((hL.grpQ j b P).le g.2)`. Take `⟨r, hr, hrg⟩` from `hg`. Set `P' : rowSG Pr sel mu` to `⟨P.1, Finset.mem_union_right _ P.2⟩`. Take `⟨h, hh⟩ : ∃ h, h = L.h j b P'` from `⟨_, rfl⟩`. Establish `hχ : (((L.levQ j b P).lam g : X.Kˣ) : X.K) = chiInv Ch sel mu cst j P' (L.h j b P') r` using `hL.chrQ j b P g r hr hrg`.

Use `replace hr : r ∈ Loc.Cbe (Jat (Pr := Pr) cst.sharp j P.1) h := hh ▸ hr`. Rewrite `hχ` using `[← hh]`. Establish `hb` using `hL.boundQ j b P' hP`. Establish `hD` using `hL.depthQ' P' hP`. Establish `hm` using `hL.hm`.

Simplify using `only [lamYat, show P'.1 ∉ Pr.vGs from hP, if_false, mem_lamY_zero] at hb`. Establish `hκ` using `hr.2`. Simplify using `only [Jat, hP, if_false] at hκ`. Establish `hκ' : ∀ x, (h⁻¹ * r * h) x ∈ stdAt X.E _ P.1 ↔ x ∈ stdAt X.E _ P.1`. Introduce `x`.

Conclude with `hκ.1 x`. Establish `hint : IntAt P.1 ((qOf P.1 : X.E) ^ j * Loc.n1Arg r)`. Use `intAt_n1Arg _ r fun x hx => ?_` and prove the remaining obligations. Establish `h1` using `(hb _ ((hκ' _).2 (hb x hx).1)).2`. Establish `h2 : h ((h⁻¹ * r * h) (h⁻¹ x)) = r x`.

Express the relevant statement in the definitionally equal form `(h * (h⁻¹ * r * h) * h⁻¹) x = r x`. Use `congr 1`. Use `group`. Rewrite `h1` using `[← hh, h2]`. Then use the resulting hypothesis. Establish `hint' : IntAt P'.1 ((qOf P'.1 : X.E) ^ cst.D P' * Loc.n1Arg r)`.

Take `⟨d, hd⟩ : ∃ d, cst.D P' = d + j` from `⟨cst.D P' - j, by omega⟩`. Rewrite using `[hd, pow_add, mul_assoc, ← Nat.cast_pow]`. Conclude with `(intAt_natCast _).mul hint`. Establish `h1` using `psi_root hL.cst_ok P' _ hint'`. Simplify using `only [chiInv, lamRow, show P'.1 ∉ Pr.vGs from hP, if_false, LocE.lamQB] at hχ`.

Establish `hne` using `((L.levQ j b P).lam g).ne_zero`. Rewrite `hne` using `[hχ]`. Take `⟨k, hk, h2⟩` from `unitV_root _ _ (fun h0 => right_ne_zero_of_mul hne (inv_eq_zero.2 h0))`. Use `⟨qOf P'.1 ^ cst.D P' * k, Nat.mul_pos (pow_pos (qOf_pos _) _) hk, Units.ext ?_⟩` and prove the remaining obligations. Rewrite using `[Units.val_pow_eq_pow_val, hχ, mul_pow, inv_pow, inv_pow, pow_mul, h1, one_pow, mul_comm _ k, pow_mul, h2, one_pow]`.

Simplify using the standard rewrite rules.
-/
theorem lam_root {X : Fields} {Pr : Primes X} {R : Ranks} {Ch : Chars X Pr R.m}
    {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ} {mu : Tup X.F X.E X.K S}
    {cst : LocCst X (rowSG Pr sel mu)} {L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))} {G : ChGlob X R.m} {m2 : ℕ}
    (hL : L.Ok Ch sel mu cst G m2) {j : ℕ} (hj : j ≤ m2 + 1) (b : L.β j)
    (P : {P // P ∈ QE sel (mu : Chr X.F X.E X.K)}) (hP : P.1 ∉ Pr.vGs) (g : (L.levQ j b P).H) :
    ∃ k : ℕ, 0 < k ∧ (L.levQ j b P).lam g ^ k = 1 := by
  classical
  have hg := Subgroup.mem_subgroupOf.1 ((hL.grpQ j b P).le g.2)
  obtain ⟨r, hr, hrg⟩ := hg
  let P' : rowSG Pr sel mu := ⟨P.1, Finset.mem_union_right _ P.2⟩
  obtain ⟨h, hh⟩ : ∃ h, h = L.h j b P' := ⟨_, rfl⟩
  have hχ : (((L.levQ j b P).lam g : X.Kˣ) : X.K) = chiInv Ch sel mu cst j P' (L.h j b P') r := hL.chrQ j b P g r hr hrg
  replace hr : r ∈ Loc.Cbe (Jat (Pr := Pr) cst.sharp j P.1) h := hh ▸ hr
  rw [← hh] at hχ
  have hb := hL.boundQ j b P' hP
  have hD := hL.depthQ' P' hP
  have hm := hL.hm
  simp only [lamYat, show P'.1 ∉ Pr.vGs from hP, if_false, mem_lamY_zero] at hb
  have hκ := hr.2
  simp only [Jat, hP, if_false] at hκ
  have hκ' : ∀ x, (h⁻¹ * r * h) x ∈ stdAt X.E _ P.1 ↔ x ∈ stdAt X.E _ P.1 := by
    intro x
    exact hκ.1 x
  have hint : IntAt P.1 ((qOf P.1 : X.E) ^ j * Loc.n1Arg r) := by
    refine intAt_n1Arg _ r fun x hx => ?_
    have h1 := (hb _ ((hκ' _).2 (hb x hx).1)).2
    have h2 : h ((h⁻¹ * r * h) (h⁻¹ x)) = r x := by
      change (h * (h⁻¹ * r * h) * h⁻¹) x = r x
      congr 1
      group
    rwa [← hh, h2] at h1
  have hint' : IntAt P'.1 ((qOf P'.1 : X.E) ^ cst.D P' * Loc.n1Arg r) := by
    obtain ⟨d, hd⟩ : ∃ d, cst.D P' = d + j := ⟨cst.D P' - j, by omega⟩
    rw [hd, pow_add, mul_assoc, ← Nat.cast_pow]
    exact (intAt_natCast _).mul hint
  have h1 := psi_root hL.cst_ok P' _ hint'
  simp only [chiInv, lamRow, show P'.1 ∉ Pr.vGs from hP, if_false, LocE.lamQB] at hχ
  have hne := ((L.levQ j b P).lam g).ne_zero
  rw [hχ] at hne
  obtain ⟨k, hk, h2⟩ := unitV_root _ _ (fun h0 => right_ne_zero_of_mul hne (inv_eq_zero.2 h0))
  refine ⟨qOf P'.1 ^ cst.D P' * k, Nat.mul_pos (pow_pos (qOf_pos _) _) hk, Units.ext ?_⟩
  rw [Units.val_pow_eq_pow_val, hχ, mul_pow, inv_pow, inv_pow, pow_mul, h1, one_pow, mul_comm _ k, pow_mul, h2, one_pow]
  simp

end GlobalTheory.GO.ChRoot
