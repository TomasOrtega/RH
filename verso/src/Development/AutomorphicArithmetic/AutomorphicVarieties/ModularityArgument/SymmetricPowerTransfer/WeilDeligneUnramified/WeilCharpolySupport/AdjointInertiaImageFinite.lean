import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.WeilDeligneUnramified.UnitaryTwoForm
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.WeilDeligneUnramified.WeilCharpolySupport.CharPolSupp
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.WeilDeligneUnramified.WeilCharpolySupport.PrinSeriesIrreducible
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.UnitaryGaloisFamilies.PlainGd
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.QuadraticCharpolyCoeffDifference
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SatWDCharPolChars

noncomputable section

open NumberField IsDedekindDomain ValuativeRel Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil
open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict
open UpperTheory.V.W (Plc Lp)
open scoped Matrix

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Z.Sym.W

open UpperTheory.V.Z.Win UpperTheory.GalN.V

/- English proof (translation)
Use `⟨Units.map e.symm.toRingHom.toMonoidHom a, Units.map e.symm.toRingHom.toMonoidHom b, ?_, ?_, ?_⟩` and prove the remaining obligations. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Apply `Polynomial.map_injective e.toRingHom e.injective` to reduce the goal to its premises. Rewrite using `[h]`.

Simplify using the standard rewrite rules.
-/
private theorem split_of_map {K K' : Type} [Field K] [Field K'] (e : K ≃+* K') {p : Polynomial K} (a b : K'ˣ)
    (h : p.map e.toRingHom = (Polynomial.X - Polynomial.C (a : K')) * (Polynomial.X - Polynomial.C (b : K'))) :
    ∃ a' b' : Kˣ, e a' = a ∧ e b' = b ∧
      p = (Polynomial.X - Polynomial.C (a' : K)) * (Polynomial.X - Polynomial.C (b' : K)) := by
  refine ⟨Units.map e.symm.toRingHom.toMonoidHom a, Units.map e.symm.toRingHom.toMonoidHom b, ?_, ?_, ?_⟩
  · simp
  · simp
  · apply Polynomial.map_injective e.toRingHom e.injective
    rw [h]
    simp

/- English proof (translation)
Substitute `h` using the available equality. Simplify using the standard rewrite rules.
-/
private theorem roots3 {K : Type} [Field K] {p : Polynomial K} {a b c : K}
    (h : p = (Polynomial.X - Polynomial.C a) * (Polynomial.X - Polynomial.C b) * (Polynomial.X - Polynomial.C c)) :
    p.IsRoot a ∧ p.IsRoot b ∧ p.IsRoot c := by
  subst h
  simp

/- English proof (translation)
Apply the tactic sequence `rcases hj with rfl | rfl <;> rcases hQ with e | e`. Conclude with `hn _ _ r0 r1 1 le_rfl (by simpa using e)`. Conclude with `hn _ _ r1 r0 1 le_rfl (by`. Simplify using `only [pow_one] at e ⊢`. Rewrite using `[mul_comm (Q : Qbar l), e])`.

Conclude with `hn _ _ r0 r2 1 le_rfl (by`. Rewrite using `[pow_one, pow_one, ← e]`. Use the proof step `field_simp)`. Conclude with `hn _ _ r2 r0 1 le_rfl (by`. Rewrite using `[pow_one, pow_one]`.

Conclude with `inv_eq_of_mul_eq_one_right (by linear_combination e))`.
-/
private theorem link_false {l : ℕ} [Fact l.Prime] {x : Matrix.GeneralLinearGroup (Fin 3) (Qbar l)} {Q : ℕ} (hn : NoLink x Q) (c : Qbar l) (h0 : c ≠ 0)
    (r0 : x.val.charpoly.IsRoot c)
    (r1 : x.val.charpoly.IsRoot 1)
    (r2 : x.val.charpoly.IsRoot c⁻¹)
    {j : ℕ} (hj : j = 1 ∨ j = 2) (hQ : c ^ j = Q ∨ c ^ j * Q = 1) : False := by
  rcases hj with rfl | rfl <;> rcases hQ with e | e
  · exact hn _ _ r0 r1 1 le_rfl (by simpa using e)
  · exact hn _ _ r1 r0 1 le_rfl (by
      simp only [pow_one] at e ⊢
      rw [mul_comm (Q : Qbar l), e])
  · exact hn _ _ r0 r2 1 le_rfl (by
      rw [pow_one, pow_one, ← e]
      field_simp)
  · exact hn _ _ r2 r0 1 le_rfl (by
      rw [pow_one, pow_one]
      exact inv_eq_of_mul_eq_one_right (by linear_combination e))

section
variable {L Ω : Type} [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 L)} {h : IsPlaceOver A w} {l : ℕ} [Fact l.Prime]

/- English proof (translation)
Establish `hw` using `hx.wdOf_eq hl`. Take `⟨t, ht, φ, hφ, N, a, hN, -⟩` from `hx`. Establish `hN0 : N = 0` using `(hN.weilDeligneParam_monodromy_eq_zero_iff hl ht ι).1 (hw ▸ hy)`. Substitute `hN0` using the available equality. Take `⟨-, U, hU, H⟩` from `hN`.

Establish `hu : ∀ σ ∈ U, ad0 r (σ : G L Ω) = 1` using `fun σ hσ => by`. Establish `h1 : r (σ : G L Ω) = 1` using `Units.ext (by rw [H σ hσ]; simp)`. Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[ad0, tw_val, MonoidHom.inv_apply, MonoidHom.comp_apply, MonoidHom.comp_apply, h1]`. Simplify using the standard rewrite rules.

Use `haveI := compactSpace_Ine (E := L) A`. Set `f` to `(ad0 r).comp (Ine (F := L) A).subtype`. Use `haveI : Finite (Ine (F := L) A ⧸ f.ker) := Subgroup.quotient_finite_of_isOpen _ (Subgroup.isOpen_mono (H₁ := U) (fun x hx => hu x hx) hU)`. Use `haveI : Finite f.range := Finite.of_equiv _ (QuotientGroup.quotientKerEquivRange f).toEquiv`. Use `(Set.toFinite (f.range : Set (GL (Fin 3) (Qbar l)))).subset ?_` and prove the remaining obligations.

Introduce and unpack `_ ⟨s, hs, rfl⟩`. Conclude with `⟨⟨s, hs⟩, rfl⟩`.
-/
private theorem adjoint_inertia_image_finite (hl : ((l : ℕ) : 𝓞 L) ∉ w.asIdeal) {ι : Qbar l ≃+* ℂ} {r : G L Ω →* GL (Fin 2) (Qbar l)}
    {y : WD h} (hx : IsWDOf ι r y) (hy : y.mono0) : (ad0 r '' (Ine (F := L) A : Set (G L Ω))).Finite := by
  have hw := hx.wdOf_eq hl
  obtain ⟨t, ht, φ, hφ, N, a, hN, -⟩ := hx
  have hN0 : N = 0 := (hN.weilDeligneParam_monodromy_eq_zero_iff hl ht ι).1 (hw ▸ hy)
  subst hN0
  obtain ⟨-, U, hU, H⟩ := hN
  have hu : ∀ σ ∈ U, ad0 r (σ : G L Ω) = 1 := fun σ hσ => by
    have h1 : r (σ : G L Ω) = 1 := Units.ext (by rw [H σ hσ]; simp)
    apply Units.ext
    rw [ad0, tw_val, MonoidHom.inv_apply, MonoidHom.comp_apply, MonoidHom.comp_apply, h1]
    simp
  haveI := compactSpace_Ine (E := L) A
  let f := (ad0 r).comp (Ine (F := L) A).subtype
  haveI : Finite (Ine (F := L) A ⧸ f.ker) :=
    Subgroup.quotient_finite_of_isOpen _ (Subgroup.isOpen_mono (H₁ := U) (fun x hx => hu x hx) hU)
  haveI : Finite f.range := Finite.of_equiv _ (QuotientGroup.quotientKerEquivRange f).toEquiv
  refine (Set.toFinite (f.range : Set (GL (Fin 3) (Qbar l)))).subset ?_
  rintro _ ⟨s, hs, rfl⟩
  exact ⟨⟨s, hs⟩, rfl⟩
end

end UpperTheory.V.Z.Sym.W

open UpperTheory.V.Z.Win UpperTheory.GalN.V in
/- English proof (translation)
Introduce `P L Ω _ _ _ _ _ l _ ι r hr hU w hl τ hg hT`. Take `⟨ψ, hψ, ⟨e⟩, -⟩` from `psOf P.litN L 2 w τ hT`. Use `⟨ψ, hψ, ⟨e⟩, ?_⟩` and prove the remaining obligations. Introduce `j hj ε hε hlk`. Take `⟨A, h⟩` from `ReciprocityTheory.Gal.exists_isPlaceOver Ω w`.

Take `⟨rc, hrc⟩` from `exRec' P.litN h`. Establish `gd : Gd (rc (algNorm τ))` using `Gu.plainGd L Ω A w h rc hrc 2 τ hT`. Establish `hx : IsWDOf ι r (rc (algNorm τ))` using `((hg A h rc hrc).1 hl).isWDOf gd`. Take `⟨a, ha, -⟩` from `id hrc`. Take `⟨s, j', hj', hs, hn⟩` from `hU w hl A h (adjoint_inertia_image_finite hl hx gd.2)`.

Establish `hact : ActsAs A (normV w) s j' 0`. Simplify using `only [ActsAs, pow_zero, pow_one]`. Conclude with `hs`. Set `S : Weil h` to `⟨s, j', 0, hact⟩`. Establish `hd : deg S = (j' : ℤ)` using `by simpa using deg_eq (σ := S) hact`.

Establish `hcp` using `eigW P L Ω l ι 2 r w hl A h a ha τ hg hT ψ hψ (.of_injective e.toIntertwiningMap e.toLinearEquiv.injective) S`. Rewrite `hcp` using `[psPol, Fin.prod_univ_two]`. Take `⟨a', b', ea, eb, hab⟩` from `split_of_map ι _ _ hcp`. Establish `hc` using `(ad0Facts l (G L Ω) r).2.2.2.2.1 s a' b' hab`. Take `⟨r0, r1, r2⟩` from `roots3 hc`.

Establish `hci : ((b' / a' : (Qbar l)ˣ) : Qbar l) = (((a' / b' : (Qbar l)ˣ) : Qbar l))⁻¹`. Rewrite using `[← Units.val_inv_eq_inv_val, inv_div]`. Rewrite `r2` using `[hci]`. Use `link_false hn _ (Units.ne_zero _) r0 r1 r2 hj ?_` and prove the remaining obligations. Establish `hc' : ι ((a' / b' : (Qbar l)ˣ) : Qbar l) = ((ψ 0 (a S) / ψ 1 (a S) : ℂˣ) : ℂ)`.

Rewrite using `[Units.val_div_eq_div_val, map_div₀, ea, eb, ← Units.val_div_eq_div_val, mul_div_mul_right_eq_div]`. Establish `hv : (ψ 0 (a S) / ψ 1 (a S)) ^ j = absPow (w.adicCompletion L) (ε : ℂ) (a S)`. Rewrite using `[← hlk]`. Both sides reduce to the same expression. Establish `hz : ι (((a' / b' : (Qbar l)ˣ) : Qbar l) ^ j) = ((absPow (w.adicCompletion L) (ε : ℂ) (a S) : ℂˣ) : ℂ)`.

Rewrite using `[map_pow, hc', ← Units.val_pow_eq_pow_val, hv]`. Break down `hε with rfl | rfl` into its components or cases. Use `left`. Apply `ι.injective` to reduce the goal to its premises. Establish `h1` using `GlobalTheory.SatChar.absPow_art ha (1 : ℝ) S`.

Rewrite `h1` using `[hd]`. Rewrite using `[hz, map_natCast]`. Simplify using `using h1`. Use `right`. Apply `ι.injective` to reduce the goal to its premises.

Establish `h1` using `GlobalTheory.SatChar.absPow_art ha (-1 : ℝ) S`. Rewrite `h1` using `[hd]`. Establish `hq : ((normV w : ℕ) : ℂ) ≠ 0`. Conclude with `(zero_lt_one.trans (one_lt_normV w)).ne'` after adjusting the coercions. Rewrite using `[map_mul, hz, map_natCast, map_one]`.

Establish `h2 : ((absPow (w.adicCompletion L) (((-1 : ℤ) : ℂ)) (a S) : ℂˣ) : ℂ) = (((normV w : ℕ) : ℂ)⁻¹) ^ j'`. Simplify `h1` using `[Complex.cpow_neg_one]`. Rewrite using `[h2]`. Use `push_cast`. Rewrite using `[inv_pow, inv_mul_cancel₀ (pow_ne_zero _ hq)]`.
-/
theorem UpperTheory.V.Z.Sym.W.awayW :
    UpperTheory.V.Z.Sym.W.AwayW := by
  intro P L Ω _ _ _ _ _ l _ ι r hr hU w hl τ hg hT
  obtain ⟨ψ, hψ, ⟨e⟩, -⟩ := psOf P.litN L 2 w τ hT
  refine ⟨ψ, hψ, ⟨e⟩, ?_⟩
  intro j hj ε hε hlk
  obtain ⟨A, h⟩ := ReciprocityTheory.Gal.exists_isPlaceOver Ω w
  obtain ⟨rc, hrc⟩ := exRec' P.litN h
  have gd : Gd (rc (algNorm τ)) := Gu.plainGd L Ω A w h rc hrc 2 τ hT
  have hx : IsWDOf ι r (rc (algNorm τ)) := ((hg A h rc hrc).1 hl).isWDOf gd
  obtain ⟨a, ha, -⟩ := id hrc
  obtain ⟨s, j', hj', hs, hn⟩ := hU w hl A h (adjoint_inertia_image_finite hl hx gd.2)
  have hact : ActsAs A (normV w) s j' 0 := by
    simp only [ActsAs, pow_zero, pow_one]
    exact hs
  let S : Weil h := ⟨s, j', 0, hact⟩
  have hd : deg S = (j' : ℤ) := by simpa using deg_eq (σ := S) hact
  have hcp := eigW P L Ω l ι 2 r w hl A h a ha τ hg hT ψ hψ
    (.of_injective e.toIntertwiningMap e.toLinearEquiv.injective) S
  rw [psPol, Fin.prod_univ_two] at hcp
  obtain ⟨a', b', ea, eb, hab⟩ := split_of_map ι _ _ hcp
  have hc := (ad0Facts l (G L Ω) r).2.2.2.2.1 s a' b' hab
  obtain ⟨r0, r1, r2⟩ := roots3 hc
  have hci : ((b' / a' : (Qbar l)ˣ) : Qbar l) = (((a' / b' : (Qbar l)ˣ) : Qbar l))⁻¹ := by
    rw [← Units.val_inv_eq_inv_val, inv_div]
  rw [hci] at r2
  refine link_false hn _ (Units.ne_zero _) r0 r1 r2 hj ?_
  have hc' : ι ((a' / b' : (Qbar l)ˣ) : Qbar l) = ((ψ 0 (a S) / ψ 1 (a S) : ℂˣ) : ℂ) := by
    rw [Units.val_div_eq_div_val, map_div₀, ea, eb, ← Units.val_div_eq_div_val, mul_div_mul_right_eq_div]
  have hv : (ψ 0 (a S) / ψ 1 (a S)) ^ j = absPow (w.adicCompletion L) (ε : ℂ) (a S) := by
    rw [← hlk]
    rfl
  have hz : ι (((a' / b' : (Qbar l)ˣ) : Qbar l) ^ j) = ((absPow (w.adicCompletion L) (ε : ℂ) (a S) : ℂˣ) : ℂ) := by
    rw [map_pow, hc', ← Units.val_pow_eq_pow_val, hv]
  rcases hε with rfl | rfl
  · left
    apply ι.injective
    have h1 := GlobalTheory.SatChar.absPow_art ha (1 : ℝ) S
    rw [hd] at h1
    rw [hz, map_natCast]
    simpa using h1
  · right
    apply ι.injective
    have h1 := GlobalTheory.SatChar.absPow_art ha (-1 : ℝ) S
    rw [hd] at h1
    have hq : ((normV w : ℕ) : ℂ) ≠ 0 := by
      exact_mod_cast (zero_lt_one.trans (one_lt_normV w)).ne'
    rw [map_mul, hz, map_natCast, map_one]
    have h2 : ((absPow (w.adicCompletion L) (((-1 : ℤ) : ℂ)) (a S) : ℂˣ) : ℂ) = (((normV w : ℕ) : ℂ)⁻¹) ^ j' := by
      simpa [Complex.cpow_neg_one] using h1
    rw [h2]
    push_cast
    rw [inv_pow, inv_mul_cancel₀ (pow_ne_zero _ hq)]
