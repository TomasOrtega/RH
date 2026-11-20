import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.CrystallineCardinalities.UnitStep
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.CrystallineCardinalities.CjFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.CrystallineCardinalities.HomBd
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.CrystallineCardinalities.HomMuLe
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.CrystallineCardinalities.OkFin

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr UpperTheory.V.Z.J

namespace UpperTheory.V.Z.J.YEx

private def matrixEntryZeroTwoSubmodule (R : Type) [CommRing R] : Submodule ℤ (Matrix (Fin 3) (Fin 3) R) where
  carrier := {X | ∀ a b, ¬ (a = 0 ∧ b = 2) → X a b = 0}
  add_mem' := fun hx hy a b h => by simp [hx a b h, hy a b h]
  zero_mem' := fun a b _ => rfl
  smul_mem' := fun c x hx a b h => by simp [hx a b h]

/- English proof (translation)
Introduce `a b h`. Rewrite using `[Matrix.single_apply, if_neg]`. Introduce and unpack `⟨rfl, rfl⟩`. Conclude with `h ⟨rfl, rfl⟩`.
-/
private theorem single_mem {R : Type} [CommRing R] (x : R) : Matrix.single (0 : Fin 3) (2 : Fin 3) x ∈ matrixEntryZeroTwoSubmodule R := by
  intro a b h
  rw [Matrix.single_apply, if_neg]
  rintro ⟨rfl, rfl⟩
  exact h ⟨rfl, rfl⟩

/- English proof (translation)
Use extensionality with `a b`. Rewrite using `[Matrix.single_apply]`. Distinguish the cases in `hab : a = 0 ∧ b = 2`. Take `⟨rfl, rfl⟩` from `hab`. Simplify using the standard rewrite rules.

Rewrite using `[if_neg (fun h' => hab ⟨h'.1.symm, h'.2.symm⟩)]`. Conclude with `h a b hab`.
-/
private theorem eq_single {R : Type} [CommRing R] {X : Matrix (Fin 3) (Fin 3) R} (h : X ∈ matrixEntryZeroTwoSubmodule R) :
    X = Matrix.single (0 : Fin 3) (2 : Fin 3) (X 0 2) := by
  ext a b
  rw [Matrix.single_apply]
  by_cases hab : a = 0 ∧ b = 2
  · obtain ⟨rfl, rfl⟩ := hab
    simp
  · rw [if_neg (fun h' => hab ⟨h'.1.symm, h'.2.symm⟩)]
    exact h a b hab

private def e02 (R : Type) [CommRing R] : R ≃+ matrixEntryZeroTwoSubmodule R where
  toFun x := ⟨Matrix.single 0 2 x, single_mem x⟩
  invFun X := X.1 0 2
  left_inv x := by simp
  right_inv X := Subtype.ext (eq_single X.2).symm
  map_add' x y := Subtype.ext (by simp [Matrix.single_add])

private def zM {R : Type} [CommRing R] (i : Fin 2) (u b : R) : Matrix (Fin 3) (Fin 3) R :=
  if i = 0 then !![u, b, 0; 0, 0, 0; 0, 0, 0] else !![0, 0, 0; 0, 0, b; 0, 0, -u]

/- English proof (translation)
Introduce `a c h`. Apply the tactic sequence `fin_cases i <;> fin_cases a <;> fin_cases c <;> simp [zM] at h ⊢`.
-/
private theorem zM_upT {R : Type} [CommRing R] (i : Fin 2) (u b : R) : UpT (zM i u b) := by
  intro a c h
  fin_cases i <;> fin_cases a <;> fin_cases c <;> simp [zM] at h ⊢

/- English proof (translation)
Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [zM]`.
-/
private theorem zM_diag {R : Type} [CommRing R] (i : Fin 2) (b : R) (j : Fin 3) : zM i 0 b j j = 0 := by
  fin_cases i <;> fin_cases j <;> simp [zM]

/- English proof (translation)
Apply the tactic sequence `fin_cases i <;> simp [zM]`.
-/
private theorem zM_diff {R : Type} [CommRing R] (i : Fin 2) (u b : R) :
    zM i u b i.castSucc i.castSucc - zM i u b i.succ i.succ = u := by
  fin_cases i <;> simp [zM]

/- English proof (translation)
Substitute `h4` using the available equality. Introduce `a c h`. Establish `d0` using `h2 0`. Establish `d1` using `h2 1`. Establish `d2` using `h2 2`.

Establish `s0` using `h3 0`. Establish `s1` using `h3 1`. Establish `l10` using `h1 1 0 (by decide)`. Establish `l20` using `h1 2 0 (by decide)`. Establish `l21` using `h1 2 1 (by decide)`.

Apply the tactic sequence `fin_cases i <;> fin_cases a <;> fin_cases c <;> simp [zM] at h d0 d1 d2 s0 s1 ⊢ <;> simp [d0, d1, d2, s0, s1, l10, l20, l21] <;> abel`.
-/
private theorem zM_coc {O R : Type} [CommRing O] [CommRing R] [Module O R] (i : Fin 2) (u b u' b' b'' : R)
    (Y : Matrix (Fin 3) (Fin 3) R) (p q : Fin 2 → O) (h1 : UpT Y) (h2 : ∀ j, Y j j = zM i u' b' j j)
    (h3 : ∀ j : Fin 2, Y j.castSucc j.succ = p j • zM i u' b' j.castSucc j.succ -
      q j • (zM i u' b' j.castSucc j.castSucc - zM i u' b' j.succ j.succ))
    (h4 : b'' = b + p i • b' - q i • u') : zM i (u + u') b'' - zM i u b - Y ∈ matrixEntryZeroTwoSubmodule R := by
  subst h4
  intro a c h
  have d0 := h2 0
  have d1 := h2 1
  have d2 := h2 2
  have s0 := h3 0
  have s1 := h3 1
  have l10 := h1 1 0 (by decide)
  have l20 := h1 2 0 (by decide)
  have l21 := h1 2 1 (by decide)
  fin_cases i <;> fin_cases a <;> fin_cases c <;> simp [zM] at h d0 d1 d2 s0 s1 ⊢ <;> simp [d0, d1, d2, s0, s1, l10, l20, l21] <;> abel

/- English proof (translation)
Introduce `hn`. Take `⟨p, hp⟩` from `CharP.exists O`. Break down `CharP.char_is_prime_or_zero O p with hpp | rfl` into its components or cases. It suffices to derive a contradiction. Establish `h1 : ((p : ℕ) : ResidueField O) = 0`.

Rewrite using `[← map_natCast (residue O), CharP.cast_eq_zero O p, map_zero]`. Use `haveI : CharP (ResidueField O) l := IsCoef.char`. Rewrite `h1` using `[CharP.cast_eq_zero_iff (ResidueField O) l]`. Establish `hlp : l = p` using `(Nat.prime_dvd_prime_iff_eq (Fact.out : l.Prime) hpp).mp h1`. Substitute `hlp` using the available equality.

Conclude with `hl (CharP.cast_eq_zero O l)`. Use `haveI : CharZero O := CharP.charP_to_charZero O`. Conclude with `hn` after adjusting the coercions.
-/
private theorem natCast_ne (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O]
    (hl : (l : O) ≠ 0) (n : ℕ) : n ≠ 0 → (n : O) ≠ 0 := by
  intro hn
  obtain ⟨p, hp⟩ := CharP.exists O
  rcases CharP.char_is_prime_or_zero O p with hpp | rfl
  · exfalso
    have h1 : ((p : ℕ) : ResidueField O) = 0 := by
      rw [← map_natCast (residue O), CharP.cast_eq_zero O p, map_zero]
    haveI : CharP (ResidueField O) l := IsCoef.char
    rw [CharP.cast_eq_zero_iff (ResidueField O) l] at h1
    have hlp : l = p := (Nat.prime_dvd_prime_iff_eq (Fact.out : l.Prime) hpp).mp h1
    subst hlp
    exact hl (CharP.cast_eq_zero O l)
  · haveI : CharZero O := CharP.charP_to_charZero O
    exact_mod_cast hn

end UpperTheory.V.Z.J.YEx

open UpperTheory.V.Z.J.YEx in
/- English proof (translation)
Introduce `l _ O _ _ _ _ _ D _ _ _ _ I ε d t hl hLE hGen hT i hU`. Establish `hinv` using `(cjFacts l O D t 0 hl hT).2.1`. Take `⟨hdiag, u, β, hu, hβ, hadd, hI, ⟨s0, hs0⟩, hβc⟩` from `hU`. Take `⟨s1, hs1⟩` from `hT.dist`. Establish `hχne : (t s1 : Matrix (Fin 3) (Fin 3) O) 0 0 * (((t s1)⁻¹ : GL (Fin 3) O) : Matrix (Fin 3) (Fin 3) O) 2 2 - algebraMap ℤ_[l] O (ε s1) ≠ 0`.

Establish `h22` using `(hinv s1).2 2`. Establish `hε : algebraMap ℤ_[l] O (ε s1) ≠ 0` using `((ε s1).isUnit.map (algebraMap ℤ_[l] O)).ne_zero`. Establish `hi22 : (((t s1)⁻¹ : GL (Fin 3) O) : Matrix (Fin 3) (Fin 3) O) 2 2 ≠ 0`. Introduce `h`. Rewrite `h22` using `[h, mul_zero]`.

Conclude with `zero_ne_one h22`. Use `fin_cases i`. Establish `hd : (t s1 : Matrix (Fin 3) (Fin 3) O) 0 0 = algebraMap ℤ_[l] O (ε s1) * (t s1 : Matrix (Fin 3) (Fin 3) O) 1 1` using `hdiag s1`. Establish `key : (t s1 : Matrix (Fin 3) (Fin 3) O) 0 0 * (((t s1)⁻¹ : GL (Fin 3) O) : Matrix (Fin 3) (Fin 3) O) 2 2 - algebraMap ℤ_[l] O (ε s1) = algebraMap ℤ_[l] O (ε s1) * (((t s1)⁻¹ : GL (Fin 3) O) : Matrix (Fin 3) (Fin 3) O) 2 2 * ((t s1 : Matrix (Fin 3) (Fin 3) O) 1 1 - (t s1 : Matrix …`. Take the linear combination `(((t s1)⁻¹ : GL (Fin 3) O) : Matrix (Fin 3) (Fin 3) O) 2 2 * hd + algebraMap ℤ_[l] O (ε s1) * h22`.

Rewrite using `[key]`. Conclude with `mul_ne_zero (mul_ne_zero hε hi22) (hs1 1 2 (by decide)).ne_zero`. Establish `hd : (t s1 : Matrix (Fin 3) (Fin 3) O) 1 1 = algebraMap ℤ_[l] O (ε s1) * (t s1 : Matrix (Fin 3) (Fin 3) O) 2 2` using `hdiag s1`. Establish `key : (t s1 : Matrix (Fin 3) (Fin 3) O) 0 0 * (((t s1)⁻¹ : GL (Fin 3) O) : Matrix (Fin 3) (Fin 3) O) 2 2 - algebraMap ℤ_[l] O (ε s1) = (((t s1)⁻¹ : GL (Fin 3) O) : Matrix (Fin 3) (Fin 3) O) 2 2 * ((t s1 : Matrix (Fin 3) (Fin 3) O) 0 0 - (t s1 : Matrix (Fin 3) (Fin 3) O) 1 1)`. Take the linear combination `(((t s1)⁻¹ : GL (Fin 3) O) : Matrix (Fin 3) (Fin 3) O) 2 2 * hd + algebraMap ℤ_[l] O (ε s1) * h22`.

Rewrite using `[key]`. Conclude with `mul_ne_zero hi22 (hs1 0 1 (by decide)).ne_zero`. Use `⟨((Nat.card (O ⧸ Ideal.span {(t s1 : Matrix (Fin 3) (Fin 3) O) 0 0 * (((t s1)⁻¹ : GL (Fin 3) O) : Matrix (Fin 3) (Fin 3) O) 2 2 - algebraMap ℤ_[l] O (ε s1)})).factorial : O) * u s0, mul_ne_zero (natCast_ne l O hl _ (Nat.factorial_ne_zero _)) hs0, ?_⟩` and prove the remaining obligations. Generalize the expression as in `hC : Nat.card (O ⧸ Ideal.span {(t s1 : Matrix (Fin 3) (Fin 3) O) 0 0 * (((t s1)⁻¹ : GL (Fin 3) O) : Matrix (Fin 3) (Fin 3) O) 2 2 - algebraMap ℤ_[l] O (ε s1)}) = C`. Introduce `k hk`.

Take `⟨⟨ρ, hρ, hρopen⟩, -, hcj, hsingle, -⟩` from `cjFacts l O D t k hl hT`. Take `⟨hfin, -, hlk, -, hpow, -, -⟩` from `okFin l O hl`. Use `haveI := hfin k`. Take `⟨Nk, hNk⟩` from `hpow k`. Establish `hmk : ∀ f : D → O, AdicCont (maximalIdeal O) f → IsLocallyConstant (fun s => Ideal.Quotient.mk (Ideal.span {(l : O) ^ k}) (f s))`.

Introduce `f hf`. Establish `e : (fun s => Ideal.Quotient.mk (Ideal.span {(l : O) ^ k}) (f s)) = (Ideal.Quotient.factor hNk) ∘ (fun g => Ideal.Quotient.mk (maximalIdeal O ^ Nk) (f g))`. Use function extensionality and compare the values at `s`. Simplify using `[Ideal.Quotient.factor_mk]`. Rewrite using `[e]`.

Conclude with `(hf Nk).comp _`. Establish `hN : ∀ s, matrixEntryZeroTwoSubmodule (Ok l O k) ≤ Submodule.comap (ρ s) (matrixEntryZeroTwoSubmodule (Ok l O k))`. Introduce `s X hX`. Rewrite using `[Submodule.mem_comap, hρ, eq_single hX, hsingle]`. Conclude with `single_mem _`.

Establish `hbound : (HomMu l k ε (ρ.subrepresentation (matrixEntryZeroTwoSubmodule (Ok l O k)) hN)).ncard ≤ C`. Rewrite using `[← hC]`. Use `homBd l O D ε k _ _ (e02 (Ok l O k)) (fun s => (t s : Matrix (Fin 3) (Fin 3) O) 0 0 * (((t s)⁻¹ : GL (Fin 3) O) : Matrix (Fin 3) (Fin 3) O) 2 2) s1 hl ?_ hχne` and prove the remaining obligations. Introduce `s x`. Apply `Subtype.ext` to reduce the goal to its premises.

Use `show ρ s (Matrix.single 0 2 x) = Matrix.single 0 2 _`. Rewrite using `[hρ, hsingle]`. Establish `hzlc : IsLocallyConstant (fun s => zM i (Ideal.Quotient.mk (Ideal.span {(l : O) ^ k}) (u s)) (Ideal.Quotient.mk (Ideal.span {(l : O) ^ k}) (β s)))` using `IsLocallyConstant.comp₂ (hmk u hu) (hmk β hβ) _`. Establish `hzcoc : ∀ s s', zM i (Ideal.Quotient.mk (Ideal.span {(l : O) ^ k}) (u (s * s'))) (Ideal.Quotient.mk (Ideal.span {(l : O) ^ k}) (β (s * s'))) - zM i (Ideal.Quotient.mk (Ideal.span {(l : O) ^ k}) (u s)) (Ideal.Quotient.mk (Ideal.span {(l : O) ^ k}) (β s)) - ρ s (zM i (Ideal.Quotien …`. Introduce `s s'`.

Rewrite using `[hρ, hadd, map_add]`. Establish `hz'` using `hcj s _ (zM_upT i (Ideal.Quotient.mk (Ideal.span {(l : O) ^ k}) (u s')) (Ideal.Quotient.mk (Ideal.span {(l : O) ^ k}) (β s')))`. Use `zM_coc i _ _ _ _ _ _ (fun j => (t s : Matrix (Fin 3) (Fin 3) O) j.castSucc j.castSucc * (((t s)⁻¹ : GL (Fin 3) O) : Matrix (Fin 3) (Fin 3) O) j.succ j.succ) (fun j => (t s : Matrix (Fin 3) (Fin 3) O) j.castSucc j.succ * (((t s)⁻¹ : GL (Fin 3) O) : Matrix (Fin 3) (Fin 3) O) j.succ …` and prove the remaining obligations. Establish `hp : (t s : Matrix (Fin 3) (Fin 3) O) i.castSucc i.castSucc * (((t s)⁻¹ : GL (Fin 3) O) : Matrix (Fin 3) (Fin 3) O) i.succ i.succ = algebraMap ℤ_[l] O (ε s)`. Rewrite using `[hdiag s, mul_assoc, (hinv s).2, mul_one]`.

Use `beta_reduce`. Rewrite using `[hp, hβc, Algebra.smul_def, Algebra.smul_def, Ideal.Quotient.algebraMap_eq]`. Simplify using `only [map_add, map_sub, map_mul]`. Take `⟨y, ⟨hylc, hycoc⟩, hy⟩` from `lift l D ε d k hk hLE (Matrix (Fin 3) (Fin 3) (Ok l O k)) ρ (fun X => by ext a b; simp [hlk]) hρopen (matrixEntryZeroTwoSubmodule (Ok l O k)) hN C hbound _ hzlc hzcoc`. Establish `hyent : ∀ s (a b : Fin 3), ¬ (a = 0 ∧ b = 2) → y s a b = C.factorial • zM i (Ideal.Quotient.mk (Ideal.span {(l : O) ^ k}) (u s)) (Ideal.Quotient.mk (Ideal.span {(l : O) ^ k}) (β s)) a b`.

Introduce `s a b hab`. Establish `h` using `(hy s : ∀ a b : Fin 3, ¬ (a = 0 ∧ b = 2) → _) a b hab`. Simplify using `only [Matrix.sub_apply, Matrix.smul_apply] at h`. Conclude with `sub_eq_zero.mp h`. Establish `hnd : ∀ j : Fin 3, ¬ (j = 0 ∧ j = 2)` using `by decide`.

Use `⟨y, ?_, s0, ?_⟩` and prove the remaining obligations. Use `show IsLocallyConstant y ∧ (∀ s s', y (s * s') = y s + cj k t s (y s')) ∧ (∀ s, UpT (y s)) ∧ ∀ s ∈ I, ∀ j : Fin 3, y s j j = 0`. Use `⟨hylc, fun s s' => by rw [hycoc, hρ], ?_, ?_⟩` and prove the remaining obligations. Introduce `s a b hab`. Rewrite using `[hyent s a b ?_, zM_upT i _ _ a b hab, smul_zero]`.

Introduce and unpack `⟨rfl, rfl⟩`. Conclude with `absurd hab (by decide)`. Introduce `s hs j`. Rewrite using `[hyent s j j (hnd j), hI s hs, map_zero, zM_diag, smul_zero]`. Rewrite using `[hyent s0 _ _ (hnd _), hyent s0 _ _ (hnd _), ← smul_sub, zM_diff, nsmul_eq_mul, map_mul, map_natCast]`.
-/
theorem UpperTheory.V.Z.J.yEx :
    ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (D : Type) [Group D] [TopologicalSpace D] [IsTopologicalGroup D] [CompactSpace D] (I : Subgroup D) (ε : D →* ℤ_[l]ˣ) (d : ℕ) (t : D →* GL (Fin 3) O), (l : O) ≠ 0 → LE l D ε d → GenI l I d → TriRep t → ∀ i : Fin 2, UnitStep I ε t i → ∃ c : O, c ≠ 0 ∧ ∀ k, 0 < k → ∃ y ∈ ZF (l := l) I k t, ∃ s, y s i.castSucc i.castSucc - y s i.succ i.succ = Ideal.Quotient.mk _ c := by
  intro l _ O _ _ _ _ _ D _ _ _ _ I ε d t hl hLE hGen hT i hU
  have hinv := (cjFacts l O D t 0 hl hT).2.1
  obtain ⟨hdiag, u, β, hu, hβ, hadd, hI, ⟨s0, hs0⟩, hβc⟩ := hU
  obtain ⟨s1, hs1⟩ := hT.dist
  have hχne : (t s1 : Matrix (Fin 3) (Fin 3) O) 0 0 * (((t s1)⁻¹ : GL (Fin 3) O) : Matrix (Fin 3) (Fin 3) O) 2 2
      - algebraMap ℤ_[l] O (ε s1) ≠ 0 := by
    have h22 := (hinv s1).2 2
    have hε : algebraMap ℤ_[l] O (ε s1) ≠ 0 := ((ε s1).isUnit.map (algebraMap ℤ_[l] O)).ne_zero
    have hi22 : (((t s1)⁻¹ : GL (Fin 3) O) : Matrix (Fin 3) (Fin 3) O) 2 2 ≠ 0 := by
      intro h
      rw [h, mul_zero] at h22
      exact zero_ne_one h22
    fin_cases i
    · have hd : (t s1 : Matrix (Fin 3) (Fin 3) O) 0 0
          = algebraMap ℤ_[l] O (ε s1) * (t s1 : Matrix (Fin 3) (Fin 3) O) 1 1 := hdiag s1
      have key : (t s1 : Matrix (Fin 3) (Fin 3) O) 0 0 * (((t s1)⁻¹ : GL (Fin 3) O) : Matrix (Fin 3) (Fin 3) O) 2 2
          - algebraMap ℤ_[l] O (ε s1) = algebraMap ℤ_[l] O (ε s1) * (((t s1)⁻¹ : GL (Fin 3) O) : Matrix (Fin 3) (Fin 3) O) 2 2
            * ((t s1 : Matrix (Fin 3) (Fin 3) O) 1 1 - (t s1 : Matrix (Fin 3) (Fin 3) O) 2 2) := by
        linear_combination (((t s1)⁻¹ : GL (Fin 3) O) : Matrix (Fin 3) (Fin 3) O) 2 2 * hd
          + algebraMap ℤ_[l] O (ε s1) * h22
      rw [key]
      exact mul_ne_zero (mul_ne_zero hε hi22) (hs1 1 2 (by decide)).ne_zero
    · have hd : (t s1 : Matrix (Fin 3) (Fin 3) O) 1 1
          = algebraMap ℤ_[l] O (ε s1) * (t s1 : Matrix (Fin 3) (Fin 3) O) 2 2 := hdiag s1
      have key : (t s1 : Matrix (Fin 3) (Fin 3) O) 0 0 * (((t s1)⁻¹ : GL (Fin 3) O) : Matrix (Fin 3) (Fin 3) O) 2 2
          - algebraMap ℤ_[l] O (ε s1) = (((t s1)⁻¹ : GL (Fin 3) O) : Matrix (Fin 3) (Fin 3) O) 2 2
            * ((t s1 : Matrix (Fin 3) (Fin 3) O) 0 0 - (t s1 : Matrix (Fin 3) (Fin 3) O) 1 1) := by
        linear_combination (((t s1)⁻¹ : GL (Fin 3) O) : Matrix (Fin 3) (Fin 3) O) 2 2 * hd
          + algebraMap ℤ_[l] O (ε s1) * h22
      rw [key]
      exact mul_ne_zero hi22 (hs1 0 1 (by decide)).ne_zero
  refine ⟨((Nat.card (O ⧸ Ideal.span {(t s1 : Matrix (Fin 3) (Fin 3) O) 0 0
      * (((t s1)⁻¹ : GL (Fin 3) O) : Matrix (Fin 3) (Fin 3) O) 2 2 - algebraMap ℤ_[l] O (ε s1)})).factorial : O) * u s0,
    mul_ne_zero (natCast_ne l O hl _ (Nat.factorial_ne_zero _)) hs0, ?_⟩
  generalize hC : Nat.card (O ⧸ Ideal.span {(t s1 : Matrix (Fin 3) (Fin 3) O) 0 0
      * (((t s1)⁻¹ : GL (Fin 3) O) : Matrix (Fin 3) (Fin 3) O) 2 2 - algebraMap ℤ_[l] O (ε s1)}) = C
  intro k hk
  obtain ⟨⟨ρ, hρ, hρopen⟩, -, hcj, hsingle, -⟩ := cjFacts l O D t k hl hT
  obtain ⟨hfin, -, hlk, -, hpow, -, -⟩ := okFin l O hl
  haveI := hfin k
  obtain ⟨Nk, hNk⟩ := hpow k
  have hmk : ∀ f : D → O, AdicCont (maximalIdeal O) f →
      IsLocallyConstant (fun s => Ideal.Quotient.mk (Ideal.span {(l : O) ^ k}) (f s)) := by
    intro f hf
    have e : (fun s => Ideal.Quotient.mk (Ideal.span {(l : O) ^ k}) (f s))
        = (Ideal.Quotient.factor hNk) ∘ (fun g => Ideal.Quotient.mk (maximalIdeal O ^ Nk) (f g)) := by
      funext s
      simp [Ideal.Quotient.factor_mk]
    rw [e]
    exact (hf Nk).comp _
  have hN : ∀ s, matrixEntryZeroTwoSubmodule (Ok l O k) ≤ Submodule.comap (ρ s) (matrixEntryZeroTwoSubmodule (Ok l O k)) := by
    intro s X hX
    rw [Submodule.mem_comap, hρ, eq_single hX, hsingle]
    exact single_mem _
  have hbound : (HomMu l k ε (ρ.subrepresentation (matrixEntryZeroTwoSubmodule (Ok l O k)) hN)).ncard ≤ C := by
    rw [← hC]
    refine homBd l O D ε k _ _ (e02 (Ok l O k))
      (fun s => (t s : Matrix (Fin 3) (Fin 3) O) 0 0 * (((t s)⁻¹ : GL (Fin 3) O) : Matrix (Fin 3) (Fin 3) O) 2 2)
      s1 hl ?_ hχne
    intro s x
    apply Subtype.ext
    show ρ s (Matrix.single 0 2 x) = Matrix.single 0 2 _
    rw [hρ, hsingle]
  have hzlc : IsLocallyConstant (fun s => zM i (Ideal.Quotient.mk (Ideal.span {(l : O) ^ k}) (u s))
      (Ideal.Quotient.mk (Ideal.span {(l : O) ^ k}) (β s))) :=
    IsLocallyConstant.comp₂ (hmk u hu) (hmk β hβ) _
  have hzcoc : ∀ s s', zM i (Ideal.Quotient.mk (Ideal.span {(l : O) ^ k}) (u (s * s')))
      (Ideal.Quotient.mk (Ideal.span {(l : O) ^ k}) (β (s * s')))
      - zM i (Ideal.Quotient.mk (Ideal.span {(l : O) ^ k}) (u s)) (Ideal.Quotient.mk (Ideal.span {(l : O) ^ k}) (β s))
      - ρ s (zM i (Ideal.Quotient.mk (Ideal.span {(l : O) ^ k}) (u s'))
          (Ideal.Quotient.mk (Ideal.span {(l : O) ^ k}) (β s'))) ∈ matrixEntryZeroTwoSubmodule (Ok l O k) := by
    intro s s'
    rw [hρ, hadd, map_add]
    have hz' := hcj s _ (zM_upT i (Ideal.Quotient.mk (Ideal.span {(l : O) ^ k}) (u s'))
      (Ideal.Quotient.mk (Ideal.span {(l : O) ^ k}) (β s')))
    refine zM_coc i _ _ _ _ _ _
      (fun j => (t s : Matrix (Fin 3) (Fin 3) O) j.castSucc j.castSucc
        * (((t s)⁻¹ : GL (Fin 3) O) : Matrix (Fin 3) (Fin 3) O) j.succ j.succ)
      (fun j => (t s : Matrix (Fin 3) (Fin 3) O) j.castSucc j.succ
        * (((t s)⁻¹ : GL (Fin 3) O) : Matrix (Fin 3) (Fin 3) O) j.succ j.succ)
      hz'.1 hz'.2.1 hz'.2.2 ?_
    have hp : (t s : Matrix (Fin 3) (Fin 3) O) i.castSucc i.castSucc
        * (((t s)⁻¹ : GL (Fin 3) O) : Matrix (Fin 3) (Fin 3) O) i.succ i.succ = algebraMap ℤ_[l] O (ε s) := by
      rw [hdiag s, mul_assoc, (hinv s).2, mul_one]
    beta_reduce
    rw [hp, hβc, Algebra.smul_def, Algebra.smul_def, Ideal.Quotient.algebraMap_eq]
    simp only [map_add, map_sub, map_mul]
  obtain ⟨y, ⟨hylc, hycoc⟩, hy⟩ := lift l D ε d k hk hLE (Matrix (Fin 3) (Fin 3) (Ok l O k)) ρ
    (fun X => by ext a b; simp [hlk]) hρopen (matrixEntryZeroTwoSubmodule (Ok l O k)) hN C hbound _ hzlc hzcoc
  have hyent : ∀ s (a b : Fin 3), ¬ (a = 0 ∧ b = 2) → y s a b = C.factorial •
      zM i (Ideal.Quotient.mk (Ideal.span {(l : O) ^ k}) (u s)) (Ideal.Quotient.mk (Ideal.span {(l : O) ^ k}) (β s)) a b := by
    intro s a b hab
    have h := (hy s : ∀ a b : Fin 3, ¬ (a = 0 ∧ b = 2) → _) a b hab
    simp only [Matrix.sub_apply, Matrix.smul_apply] at h
    exact sub_eq_zero.mp h
  have hnd : ∀ j : Fin 3, ¬ (j = 0 ∧ j = 2) := by decide
  refine ⟨y, ?_, s0, ?_⟩
  · show IsLocallyConstant y ∧ (∀ s s', y (s * s') = y s + cj k t s (y s')) ∧ (∀ s, UpT (y s)) ∧
      ∀ s ∈ I, ∀ j : Fin 3, y s j j = 0
    refine ⟨hylc, fun s s' => by rw [hycoc, hρ], ?_, ?_⟩
    · intro s a b hab
      rw [hyent s a b ?_, zM_upT i _ _ a b hab, smul_zero]
      rintro ⟨rfl, rfl⟩
      exact absurd hab (by decide)
    · intro s hs j
      rw [hyent s j j (hnd j), hI s hs, map_zero, zM_diag, smul_zero]
  · rw [hyent s0 _ _ (hnd _), hyent s0 _ _ (hnd _), ← smul_sub, zM_diff, nsmul_eq_mul, map_mul, map_natCast]
