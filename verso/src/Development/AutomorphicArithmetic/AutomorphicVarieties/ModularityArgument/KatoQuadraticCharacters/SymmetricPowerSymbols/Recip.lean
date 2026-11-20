import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.SymExOf
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SpecialLinearGroupIntMapZmodSurjective

open scoped MatrixGroups Matrix
open GlobalTheory.KZ GlobalTheory.K4 UpperTheory.V.Z.Kato.Sym

/- English proof (translation)
Introduce `Ω _ _ _ ε X s γ S`. Use `choose L hL hLf using X.level`. Use `set M : ℕ := ∏ f ∈ S, L f with hMdef`. Establish `hM : 0 < M` using `Finset.prod_pos fun f _ => hL f`. Establish `hfix : ∀ f ∈ S, ∀ δ ∈ CongruenceSubgroup.Gamma M, X.sl (ofSL δ) f = f`.

Introduce `f hf δ hδ`. Apply `hLf f δ` to reduce the goal to its premises. Establish `hd : L f ∣ M` using `Finset.dvd_prod_of_mem _ hf`. Rewrite `hδ`, the goal using `[CongruenceSubgroup.Gamma_mem]`. Take `⟨h1, h2, h3, h4⟩` from `hδ`.

Establish `c1` using `congrArg (ZMod.castHom hd (ZMod (L f))) h1`. Establish `c2` using `congrArg (ZMod.castHom hd (ZMod (L f))) h2`. Establish `c3` using `congrArg (ZMod.castHom hd (ZMod (L f))) h3`. Establish `c4` using `congrArg (ZMod.castHom hd (ZMod (L f))) h4`. Rewrite `c1`, `c2`, `c3`, `c4` using `[map_intCast]`.

Rewrite `c1`, `c4` using `[map_one]`. Rewrite `c2`, `c3` using `[map_zero]`. Conclude with `⟨c1, c2, c3, c4⟩`. Use `haveI : NeZero M := ⟨hM.ne'⟩`. Use `haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ`.

Use `haveI : CharZero Ω := algebraRat.charZero Ω`. Use `haveI : NeZero (M : Ω) := ⟨by exact_mod_cast hM.ne'⟩`. Take `⟨ζ, hζ⟩` from `HasEnoughRootsOfUnity.exists_primitiveRoot Ω M`. Establish `hex : ∀ t : Ω ≃ₐ[ℚ] Ω, ∃ d : ℕ, t ζ = ζ ^ d` using `fun t => by`. Take `⟨i, -, hi⟩` from `hζ.eq_pow_of_pow_eq_one (ξ := t ζ) (by rw [← map_pow, hζ.pow_eq_one, map_one])`.

Conclude with `⟨i, hi.symm⟩`. Take `⟨d, hd⟩` from `hex s`. Take `⟨e, he⟩` from `hex s.symm`. Establish `hde : (d : ZMod M) * e = 1`. Establish `h1 : ζ ^ (d * e) = ζ ^ 1`.

Rewrite using `[pow_mul, ← hd, ← map_pow, ← he]`. Simplify using the standard rewrite rules. Establish `h2` using `(hζ.isOfFinOrder hM.ne').pow_eq_pow_iff_modEq.mp h1`. Rewrite `h2` using `[← hζ.eq_orderOf]`. Use `(ZMod.natCast_eq_natCast_iff _ _ _).mpr h2` as an intermediate fact.

Simplify using `using this`. Establish `hdet : ((en γ 0 0 : ℤ) : ZMod M) * en γ 1 1 - (en γ 0 1 : ℤ) * (en γ 1 0 : ℤ) = 1`. Establish `h` using `γ.det_coe`. Rewrite `h` using `[Matrix.det_fin_two]`. Use `congrArg (Int.cast : ℤ → ZMod M) h` as an intermediate fact.

Simplify `this` using `[en]`. Set `A : SL(2, ZMod M)` to `⟨!![(en γ 0 0 : ℤ), e * (en γ 0 1 : ℤ); d * (en γ 1 0 : ℤ), (en γ 1 1 : ℤ)], by`. Rewrite using `[Matrix.det_fin_two_of]`. Take the linear combination `hdet - ((en γ 0 1 : ℤ) : ZMod M) * (en γ 1 0 : ℤ) * hde⟩`. Take `⟨γ', hγ'⟩` from `GlobalTheory.specialLinearGroup_map_intCast_zmod_surjective M A`.

Establish `hent : ∀ i j, ((en γ' i j : ℤ) : ZMod M) = A.1 i j` using `fun i j => by`. Rewrite using `[← hγ']`. Both sides reduce to the same expression. Use `⟨γ', fun f hf => (X.recip M f hM (hfix f hf) ζ hζ s d (by rw [hd, zpow_natCast]) γ' γ ?_).symm⟩` and prove the remaining obligations. Rewrite using `[hent, hent, hent, hent]`.

Use `⟨by simp [A], ?_, by simp [A], by simp [A]⟩` and prove the remaining obligations. Establish `: A.1 0 1 = e * (en γ 0 1 : ℤ)` using `by simp [A]`. Rewrite using `[this]`. Use `push_cast`. Take the linear combination `-((en γ 0 1 : ℤ) : ZMod M) * hde`.
-/
theorem UpperTheory.V.Z.Kato.Sym.recip :
    UpperTheory.V.Z.Kato.Sym.Recip := by
  classical
  intro Ω _ _ _ ε X s γ S
  choose L hL hLf using X.level
  set M : ℕ := ∏ f ∈ S, L f with hMdef
  have hM : 0 < M := Finset.prod_pos fun f _ => hL f
  have hfix : ∀ f ∈ S, ∀ δ ∈ CongruenceSubgroup.Gamma M, X.sl (ofSL δ) f = f := by
    intro f hf δ hδ
    apply hLf f δ
    have hd : L f ∣ M := Finset.dvd_prod_of_mem _ hf
    rw [CongruenceSubgroup.Gamma_mem] at hδ ⊢
    obtain ⟨h1, h2, h3, h4⟩ := hδ
    have c1 := congrArg (ZMod.castHom hd (ZMod (L f))) h1
    have c2 := congrArg (ZMod.castHom hd (ZMod (L f))) h2
    have c3 := congrArg (ZMod.castHom hd (ZMod (L f))) h3
    have c4 := congrArg (ZMod.castHom hd (ZMod (L f))) h4
    rw [map_intCast] at c1 c2 c3 c4
    rw [map_one] at c1 c4
    rw [map_zero] at c2 c3
    exact ⟨c1, c2, c3, c4⟩
  haveI : NeZero M := ⟨hM.ne'⟩
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : CharZero Ω := algebraRat.charZero Ω
  haveI : NeZero (M : Ω) := ⟨by exact_mod_cast hM.ne'⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω M
  have hex : ∀ t : Ω ≃ₐ[ℚ] Ω, ∃ d : ℕ, t ζ = ζ ^ d := fun t => by
    obtain ⟨i, -, hi⟩ := hζ.eq_pow_of_pow_eq_one (ξ := t ζ) (by rw [← map_pow, hζ.pow_eq_one, map_one])
    exact ⟨i, hi.symm⟩
  obtain ⟨d, hd⟩ := hex s
  obtain ⟨e, he⟩ := hex s.symm
  have hde : (d : ZMod M) * e = 1 := by
    have h1 : ζ ^ (d * e) = ζ ^ 1 := by
      rw [pow_mul, ← hd, ← map_pow, ← he]; simp
    have h2 := (hζ.isOfFinOrder hM.ne').pow_eq_pow_iff_modEq.mp h1
    rw [← hζ.eq_orderOf] at h2
    have := (ZMod.natCast_eq_natCast_iff _ _ _).mpr h2
    simpa using this
  have hdet : ((en γ 0 0 : ℤ) : ZMod M) * en γ 1 1 - (en γ 0 1 : ℤ) * (en γ 1 0 : ℤ) = 1 := by
    have h := γ.det_coe
    rw [Matrix.det_fin_two] at h
    have := congrArg (Int.cast : ℤ → ZMod M) h
    simpa [en] using this
  let A : SL(2, ZMod M) := ⟨!![(en γ 0 0 : ℤ), e * (en γ 0 1 : ℤ); d * (en γ 1 0 : ℤ), (en γ 1 1 : ℤ)], by
    rw [Matrix.det_fin_two_of]
    linear_combination hdet - ((en γ 0 1 : ℤ) : ZMod M) * (en γ 1 0 : ℤ) * hde⟩
  obtain ⟨γ', hγ'⟩ := GlobalTheory.specialLinearGroup_map_intCast_zmod_surjective M A
  have hent : ∀ i j, ((en γ' i j : ℤ) : ZMod M) = A.1 i j := fun i j => by
    rw [← hγ']; rfl
  refine ⟨γ', fun f hf => (X.recip M f hM (hfix f hf) ζ hζ s d (by rw [hd, zpow_natCast]) γ' γ ?_).symm⟩
  rw [hent, hent, hent, hent]
  refine ⟨by simp [A], ?_, by simp [A], by simp [A]⟩
  have : A.1 0 1 = e * (en γ 0 1 : ℤ) := by simp [A]
  rw [this]
  push_cast
  linear_combination -((en γ 0 1 : ℤ) : ZMod M) * hde
