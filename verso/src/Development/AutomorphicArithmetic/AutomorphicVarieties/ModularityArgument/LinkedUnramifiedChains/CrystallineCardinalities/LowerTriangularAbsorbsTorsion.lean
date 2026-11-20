import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.CrystallineCardinalities.UnitStep
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.CrystallineCardinalities.CjFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.CrystallineCardinalities.OkFin
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.CrystallineCardinalities.DualCard
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.CrystallineCardinalities.WtCut

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr UpperTheory.V.Z.J

/- English proof (translation)
Use `haveI : NeZero (l ^ k) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩`. Take `⟨hZfin, hZcard⟩` from `hLE k hk N ρ hN hρ`. Use `⟨hZfin, ?_⟩` and prove the remaining obligations. Establish `h0 : (0 : D → N) ∈ Zc ρ` using `⟨IsLocallyConstant.const 0, fun s t => by simp⟩`. Take `⟨hdA, hcA⟩` from `dualCard l k A hA`.

Take `⟨hdN, -⟩` from `dualCard l k N hN`. Use `haveI := hdA`. Use `haveI := hdN`. Establish `hHom : Nat.card A ≤ (HomMu l k ε ρ).ncard`. Rewrite using `[← hcA, ← Set.ncard_univ]`.

Use `Set.ncard_le_ncard_of_injOn (fun φ => φ.comp e) ?_ ?_ (Set.toFinite _)` and prove the remaining obligations. Introduce `φ _ s x show φ (e (ρ s x)) = _ * φ (e x)`. Rewrite using `[hε, map_nsmul, nsmul_eq_mul, ZMod.natCast_zmod_val]`. Introduce `φ _ ψ _ h`. Conclude with `(AddMonoidHom.cancel_right he).1 h`.

Establish `hbig : Nat.card A ^ (6 + 5 * d) ≤ (Zc ρ).ncard`. Rewrite using `[hZcard]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← pow_mul, ← pow_succ]`. Use `congr 1`.

Expand and normalize the polynomial expressions, which then agree. Use `_ ≤ Nat.card N ^ (1 + d) * (HomMu l k ε ρ).ncard := Nat.mul_le_mul (Nat.pow_le_pow_left hc _) hHom`. Set `Z : AddSubgroup (D → N)` to `{ carrier := Zc ρ add_mem' := fun {a b} ha hb => ⟨ha.1.add hb.1, fun s t => by`. Simplify using `only [Pi.add_apply, ha.2 s t, hb.2 s t, map_add]`. Use the proof step `abel⟩`.

Use the proof step `zero_mem' := h0`. Use the proof step `neg_mem' := fun {a} ha => ⟨ha.1.neg, fun s t => by`. Simplify using `only [Pi.neg_apply, ha.2 s t, map_neg]`. Use the proof step `abel⟩ }`. Use `haveI : Finite Z := hZfin.to_subtype`.

Establish `hpZ : ∀ z ∈ Z, IsLocallyConstant z ∧ ∀ (j : Fin 2) (s s' : D), p j (z (s * s')) = p j (z s) + p j (z s')`. Introduce `z hz`. Establish `hz' : z ∈ Zc ρ` using `hz`. Use `⟨hz'.1, fun j s s' => ?_⟩` and prove the remaining obligations. Rewrite using `[hz'.2 s s', map_add, hp]`.

Establish `hcut` using `wtCut l D I d k 2 A N hG hA Z inferInstance p hpZ`. Establish `hZc : Nat.card Z = (Zc ρ).ncard` using `Nat.card_coe_set_eq (Zc ρ)`. Establish `hApos : 0 < Nat.card A ^ (2 * d)` using `pow_pos Nat.card_pos _`. Use `Nat.le_of_mul_le_mul_right ?_ hApos` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[← pow_add]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Use `_ ≤ (Zc ρ).ncard := hbig`. Use `_ = Nat.card Z := hZc.symm`.

Use `_ ≤ _ := hcut`.
-/
private theorem lower_triangular_absorbs_torsion (l : ℕ) [Fact l.Prime] (D : Type) [Group D] [TopologicalSpace D] (I : Subgroup D)
    (ε : D →* ℤ_[l]ˣ) (d k : ℕ) (hk : 0 < k) (hLE : LE l D ε d) (hG : GenI l I d)
    (A N : Type) [AddCommGroup A] [Finite A] [AddCommGroup N] [Finite N]
    (hA : ∀ x : A, l ^ k • x = 0) (hN : ∀ x : N, l ^ k • x = 0) (ρ : Representation ℤ D N)
    (hρ : IsOpen (ρ.ker : Set D)) (hc : Nat.card A ^ 5 ≤ Nat.card N) (e : N →+ A) (he : Function.Surjective e)
    (hε : ∀ s x, e (ρ s x) = (PadicInt.toZModPow k (ε s : ℤ_[l])).val • e x)
    (p : Fin 2 → N →+ A) (hp : ∀ j s x, p j (ρ s x) = p j x) :
    (Zc ρ).Finite ∧ Nat.card A ^ (6 + 3 * d) ≤ {z | z ∈ Zc ρ ∧ ∀ j, ∀ s ∈ I, p j (z s) = 0}.ncard := by
  classical
  haveI : NeZero (l ^ k) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  obtain ⟨hZfin, hZcard⟩ := hLE k hk N ρ hN hρ
  refine ⟨hZfin, ?_⟩
  have h0 : (0 : D → N) ∈ Zc ρ := ⟨IsLocallyConstant.const 0, fun s t => by simp⟩
  obtain ⟨hdA, hcA⟩ := dualCard l k A hA
  obtain ⟨hdN, -⟩ := dualCard l k N hN
  haveI := hdA
  haveI := hdN
  have hHom : Nat.card A ≤ (HomMu l k ε ρ).ncard := by
    rw [← hcA, ← Set.ncard_univ]
    refine Set.ncard_le_ncard_of_injOn (fun φ => φ.comp e) ?_ ?_ (Set.toFinite _)
    · intro φ _ s x
      show φ (e (ρ s x)) = _ * φ (e x)
      rw [hε, map_nsmul, nsmul_eq_mul, ZMod.natCast_zmod_val]
    · intro φ _ ψ _ h
      exact (AddMonoidHom.cancel_right he).1 h
  have hbig : Nat.card A ^ (6 + 5 * d) ≤ (Zc ρ).ncard := by
    rw [hZcard]
    calc Nat.card A ^ (6 + 5 * d) = (Nat.card A ^ 5) ^ (1 + d) * Nat.card A := by
          rw [← pow_mul, ← pow_succ]; congr 1; ring
      _ ≤ Nat.card N ^ (1 + d) * (HomMu l k ε ρ).ncard :=
          Nat.mul_le_mul (Nat.pow_le_pow_left hc _) hHom
  let Z : AddSubgroup (D → N) :=
    { carrier := Zc ρ
      add_mem' := fun {a b} ha hb => ⟨ha.1.add hb.1, fun s t => by
        simp only [Pi.add_apply, ha.2 s t, hb.2 s t, map_add]; abel⟩
      zero_mem' := h0
      neg_mem' := fun {a} ha => ⟨ha.1.neg, fun s t => by
        simp only [Pi.neg_apply, ha.2 s t, map_neg]; abel⟩ }
  haveI : Finite Z := hZfin.to_subtype
  have hpZ : ∀ z ∈ Z, IsLocallyConstant z ∧
      ∀ (j : Fin 2) (s s' : D), p j (z (s * s')) = p j (z s) + p j (z s') := by
    intro z hz
    have hz' : z ∈ Zc ρ := hz
    refine ⟨hz'.1, fun j s s' => ?_⟩
    rw [hz'.2 s s', map_add, hp]
  have hcut := wtCut l D I d k 2 A N hG hA Z inferInstance p hpZ
  have hZc : Nat.card Z = (Zc ρ).ncard := Nat.card_coe_set_eq (Zc ρ)
  have hApos : 0 < Nat.card A ^ (2 * d) := pow_pos Nat.card_pos _
  refine Nat.le_of_mul_le_mul_right ?_ hApos
  calc Nat.card A ^ (6 + 3 * d) * Nat.card A ^ (2 * d) = Nat.card A ^ (6 + 5 * d) := by
        rw [← pow_add]; congr 1; ring
    _ ≤ (Zc ρ).ncard := hbig
    _ = Nat.card Z := hZc.symm
    _ ≤ _ := hcut

private def b0 (A : Type) [AddCommGroup A] (i : Fin 2) : Submodule ℤ (Matrix (Fin 3) (Fin 3) A) where
  carrier := {X | UpT X ∧ X i.castSucc i.castSucc = X i.succ i.succ}
  zero_mem' := ⟨fun _ _ _ => rfl, rfl⟩
  add_mem' := fun {a b} ha hb => ⟨fun x y h => by simp [ha.1 x y h, hb.1 x y h], by simp [ha.2, hb.2]⟩
  smul_mem' := fun c a ha => ⟨fun x y h => by simp [ha.1 x y h], by simp [ha.2]⟩

/- English proof (translation)
Establish `hlt : i.castSucc < i.succ` using `Fin.castSucc_lt_succ`. Establish `hcc : i.castSucc ≤ i.castSucc ∧ (i.castSucc, i.castSucc) ≠ (i.succ, i.succ)` using `⟨le_rfl, fun h => hlt.ne (congrArg Prod.fst h)⟩`. Set `F : ({p : Fin 3 × Fin 3 // p.1 ≤ p.2 ∧ p ≠ (i.succ, i.succ)} → A) → Matrix (Fin 3) (Fin 3) A` to `fun g a b => if h : a ≤ b ∧ (a, b) ≠ (i.succ, i.succ) then g ⟨(a, b), h⟩ else if (a, b) = (i.succ, i.succ) then g ⟨(i.castSucc, i.castSucc), hcc⟩ else 0`. Establish `hF : ∀ g, F g ∈ b0 A i`. Introduce `g`.

Use `⟨fun a b hab => ?_, ?_⟩` and prove the remaining obligations. Establish `h1 : ¬ (a ≤ b ∧ (a, b) ≠ (i.succ, i.succ))` using `fun h => absurd h.1 (not_le.mpr hab)`. Establish `h2 : (a, b) ≠ (i.succ, i.succ)`. Introduce `h`. Simplify using `only [Prod.mk.injEq] at h`.

Rewrite `hab` using `[h.1, h.2]`. Conclude with `lt_irrefl _ hab`. Simplify using `only [F, dif_neg h1, if_neg h2]`. Establish `h3 : ¬ (i.succ ≤ i.succ ∧ (i.succ, i.succ) ≠ (i.succ, i.succ))` using `fun h => h.2 rfl`. Simplify using `only [F, dif_pos hcc, dif_neg h3]`.

Simplify using the standard rewrite rules. Set `f : ({p : Fin 3 × Fin 3 // p.1 ≤ p.2 ∧ p ≠ (i.succ, i.succ)} → A) → b0 A i` to `fun g => ⟨F g, hF g⟩`. Establish `hf : Function.Injective f`. Introduce `g g' hgg`. Use function extensionality and compare the values at `⟨⟨a, b⟩, hp⟩`.

Establish `hp' : a ≤ b ∧ (a, b) ≠ (i.succ, i.succ)` using `hp`. Use `congrArg (fun x : b0 A i => (x : Matrix (Fin 3) (Fin 3) A) a b) hgg` as an intermediate fact. Simplify using `only [f, F, dif_pos hp'] at this`. Conclude with `this`. Establish `h1` using `Nat.card_le_card_of_injective f hf`.

Rewrite `h1` using `[Nat.card_fun]`. Establish `h5 : Nat.card {p : Fin 3 × Fin 3 // p.1 ≤ p.2 ∧ p ≠ (i.succ, i.succ)} = 5`. Apply the tactic sequence `rw [Nat.card_eq_fintype_card]; fin_cases i <;> decide`. Rewrite `h1` using `[h5]`. Then use the resulting hypothesis.
-/
private theorem card_borel_torsion_lower_bound (A : Type) [AddCommGroup A] [Finite A] (i : Fin 2) : Nat.card A ^ 5 ≤ Nat.card (b0 A i) := by
  classical
  have hlt : i.castSucc < i.succ := Fin.castSucc_lt_succ
  have hcc : i.castSucc ≤ i.castSucc ∧ (i.castSucc, i.castSucc) ≠ (i.succ, i.succ) :=
    ⟨le_rfl, fun h => hlt.ne (congrArg Prod.fst h)⟩
  let F : ({p : Fin 3 × Fin 3 // p.1 ≤ p.2 ∧ p ≠ (i.succ, i.succ)} → A) → Matrix (Fin 3) (Fin 3) A :=
    fun g a b => if h : a ≤ b ∧ (a, b) ≠ (i.succ, i.succ) then g ⟨(a, b), h⟩
      else if (a, b) = (i.succ, i.succ) then g ⟨(i.castSucc, i.castSucc), hcc⟩ else 0
  have hF : ∀ g, F g ∈ b0 A i := by
    intro g
    refine ⟨fun a b hab => ?_, ?_⟩
    · have h1 : ¬ (a ≤ b ∧ (a, b) ≠ (i.succ, i.succ)) := fun h => absurd h.1 (not_le.mpr hab)
      have h2 : (a, b) ≠ (i.succ, i.succ) := by
        intro h
        simp only [Prod.mk.injEq] at h
        rw [h.1, h.2] at hab
        exact lt_irrefl _ hab
      simp only [F, dif_neg h1, if_neg h2]
    · have h3 : ¬ (i.succ ≤ i.succ ∧ (i.succ, i.succ) ≠ (i.succ, i.succ)) := fun h => h.2 rfl
      simp only [F, dif_pos hcc, dif_neg h3]
      simp
  let f : ({p : Fin 3 × Fin 3 // p.1 ≤ p.2 ∧ p ≠ (i.succ, i.succ)} → A) → b0 A i := fun g => ⟨F g, hF g⟩
  have hf : Function.Injective f := by
    intro g g' hgg
    funext ⟨⟨a, b⟩, hp⟩
    have hp' : a ≤ b ∧ (a, b) ≠ (i.succ, i.succ) := hp
    have := congrArg (fun x : b0 A i => (x : Matrix (Fin 3) (Fin 3) A) a b) hgg
    simp only [f, F, dif_pos hp'] at this
    exact this
  have h1 := Nat.card_le_card_of_injective f hf
  rw [Nat.card_fun] at h1
  have h5 : Nat.card {p : Fin 3 × Fin 3 // p.1 ≤ p.2 ∧ p ≠ (i.succ, i.succ)} = 5 := by
    rw [Nat.card_eq_fintype_card]; fin_cases i <;> decide
  rwa [h5] at h1

private def ent (A : Type) [AddCommGroup A] (i : Fin 2) (a b : Fin 3) : b0 A i →+ A where
  toFun X := X.1 a b
  map_zero' := rfl
  map_add' _ _ := rfl

/- English proof (translation)
Introduce `a`. Establish `hlt : i.castSucc < i.succ` using `Fin.castSucc_lt_succ`. Use `⟨⟨Matrix.single i.castSucc i.succ a, ?_, ?_⟩, ?_⟩` and prove the remaining obligations. Introduce `x y h`. Rewrite using `[Matrix.single_apply, if_neg]`.

Introduce and unpack `⟨rfl, rfl⟩`. Conclude with `absurd h (not_lt.mpr hlt.le)`. Simplify using `[Matrix.single_apply, hlt.ne, hlt.ne']`. Use `show Matrix.single i.castSucc i.succ a i.castSucc i.succ = a`. Simplify using the standard rewrite rules.
-/
private theorem ent_surj (A : Type) [AddCommGroup A] (i : Fin 2) : Function.Surjective (ent A i i.castSucc i.succ) := by
  intro a
  have hlt : i.castSucc < i.succ := Fin.castSucc_lt_succ
  refine ⟨⟨Matrix.single i.castSucc i.succ a, ?_, ?_⟩, ?_⟩
  · intro x y h
    rw [Matrix.single_apply, if_neg]
    rintro ⟨rfl, rfl⟩
    exact absurd h (not_lt.mpr hlt.le)
  · simp [Matrix.single_apply, hlt.ne, hlt.ne']
  · show Matrix.single i.castSucc i.succ a i.castSucc i.succ = a
    simp

/- English proof (translation)
Establish `key : ∀ (R : Type) [AddCommGroup R] (i : Fin 2) (M : Matrix (Fin 3) (Fin 3) R), M i.castSucc i.castSucc = M i.succ i.succ → (∀ j : Fin 2, M (if i = 0 then j.succ else j.castSucc) (if i = 0 then j.succ else j.castSucc) = 0) → ∀ a, M a a = 0`. Introduce `R _ i M h1 h2 a`. Establish `h20` using `h2 0`. Establish `h21` using `h2 1`. Apply the tactic sequence `fin_cases i <;> fin_cases a <;> simp_all`.

Introduce `l _ O _ _ _ _ _ D _ _ _ _ I ε d t hl hLE hI hT i hU k hk`. Take `⟨hfin, -, hkill, -, -, hsmul, -⟩` from `okFin l O hl`. Use `haveI := hfin k`. Take `⟨⟨ρ, hρ, hker⟩, hinv, hcj, -⟩` from `cjFacts l O D t k hl hT`. Establish `hAm : ∀ x : Matrix (Fin 3) (Fin 3) (Ok l O k), l ^ k • x = 0` using `fun x => by`.

Use extensionality with `a b`. Simplify using `[hkill]`. Establish `hN : ∀ x : b0 (Ok l O k) i, l ^ k • x = 0` using `fun x => Subtype.ext (by rw [Submodule.coe_smul_of_tower]; exact hAm x.1)`. Establish `hmem : ∀ s (x : b0 (Ok l O k) i), ρ s x.1 ∈ b0 (Ok l O k) i` using `fun s x => by`. Take `⟨hx1, hx2⟩` from `x.2`.

Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hρ]`. Conclude with `(hcj s x.1 hx1).1`. Rewrite using `[hρ, (hcj s x.1 hx1).2.1, (hcj s x.1 hx1).2.1]`. Conclude with `hx2`.

Set `f : D → (b0 (Ok l O k) i →+ b0 (Ok l O k) i)` to `fun s => { toFun := fun x => ⟨ρ s x.1, hmem s x⟩ map_zero' := Subtype.ext (map_zero (ρ s)) map_add' := fun x y => Subtype.ext (map_add (ρ s) x.1 y.1) }`. Set `q : Fin 2 → Fin 3` to `fun j => if i = 0 then j.succ else j.castSucc`. Set `p : Fin 2 → (b0 (Ok l O k) i →+ Ok l O k)` to `fun j => ent (Ok l O k) i (q j) (q j)`. Use `le_trans (lower_triangular_absorbs_torsion l D I ε d k hk hLE hI (Ok l O k) (b0 (Ok l O k) i) (hkill k) hN { toFun := fun s => (f s).toIntLinearMap map_one' := LinearMap.ext fun x => Subtype.ext (by show ρ 1 x.1 = x.1` and prove the remaining obligations. Rewrite using `[map_one]`.

Use the proof step `rfl)`. Use the proof step `map_mul' := fun s s' => LinearMap.ext fun x => Subtype.ext (by show ρ (s * s') x.1 = ρ s (ρ s' x.1)`. Rewrite using `[map_mul]`. Use the proof step `rfl) }`. Use the proof step `?_ (card_borel_torsion_lower_bound _ i) (ent _ i i.castSucc i.succ) (ent_surj _ i) ?_ p ?_).2 ?_`.

Use `Subgroup.isOpen_mono (fun s hs => ?_) hker` and prove the remaining obligations. Rewrite `hs`, the goal using `[MonoidHom.mem_ker]`. Conclude with `LinearMap.ext fun x => Subtype.ext (by show ρ s x.1 = x.1`. Rewrite using `[hs]`. Use the proof step `rfl)`.

Introduce `s x`. Take `⟨hx1, hx2⟩` from `x.2`. Use `show ρ s x.1 i.castSucc i.succ = _ • x.1 i.castSucc i.succ`. Rewrite using `[hρ, (hcj s x.1 hx1).2.2 i, hx2, sub_self, smul_zero, sub_zero, ← hsmul k, hU.1 s, mul_assoc, (hinv s).2 i.succ, mul_one]`. Introduce `j s x show ρ s x.1 (q j) (q j) = x.1 (q j) (q j)`.

Rewrite using `[hρ, (hcj s x.1 x.2.1).2.1]`. Use `Set.ncard_le_ncard_of_injOn (fun z s => (z s).1) ?_ ?_ ?_` and prove the remaining obligations. Introduce and unpack `z ⟨hz, hI0⟩`. Use `⟨⟨hz.1.comp _, fun s s' => ?_, fun s => (z s).2.1, fun s hs a => ?_⟩, fun s => (z s).2.2⟩` and prove the remaining obligations. Use `show (z (s * s')).1 = (z s).1 + cj k t s (z s').1`.

Rewrite using `[hz.2 s s', ← hρ]`. Both sides reduce to the same expression. Conclude with `key _ i (z s).1 (z s).2.2 (fun j => hI0 j s hs) a`. Introduce `z _ z' _ h`. Use function extensionality and compare the values at `s`.

Conclude with `Subtype.ext (congrFun h s)`. Conclude with `(hLE k hk _ ρ hAm hker).1.subset (fun z hz => ⟨hz.1.1, fun s s' => by rw [hz.1.2.1, hρ]⟩)`.
-/
theorem UpperTheory.V.Z.J.low0 :
    ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (D : Type) [Group D] [TopologicalSpace D] [IsTopologicalGroup D] [CompactSpace D] (I : Subgroup D) (ε : D →* ℤ_[l]ˣ) (d : ℕ) (t : D →* GL (Fin 3) O), (l : O) ≠ 0 → LE l D ε d → GenI l I d → TriRep t → ∀ i : Fin 2, UnitStep I ε t i → ∀ k, 0 < k → Nat.card (Ok l O k) ^ (6 + 3 * d) ≤ {z | z ∈ ZF (l := l) I k t ∧ ∀ s, z s i.castSucc i.castSucc = z s i.succ i.succ}.ncard := by
  classical
  have key : ∀ (R : Type) [AddCommGroup R] (i : Fin 2) (M : Matrix (Fin 3) (Fin 3) R),
      M i.castSucc i.castSucc = M i.succ i.succ →
      (∀ j : Fin 2, M (if i = 0 then j.succ else j.castSucc) (if i = 0 then j.succ else j.castSucc) = 0) →
      ∀ a, M a a = 0 := by
    intro R _ i M h1 h2 a
    have h20 := h2 0
    have h21 := h2 1
    fin_cases i <;> fin_cases a <;> simp_all
  intro l _ O _ _ _ _ _ D _ _ _ _ I ε d t hl hLE hI hT i hU k hk
  obtain ⟨hfin, -, hkill, -, -, hsmul, -⟩ := okFin l O hl
  haveI := hfin k
  obtain ⟨⟨ρ, hρ, hker⟩, hinv, hcj, -⟩ := cjFacts l O D t k hl hT
  have hAm : ∀ x : Matrix (Fin 3) (Fin 3) (Ok l O k), l ^ k • x = 0 := fun x => by
    ext a b; simp [hkill]
  have hN : ∀ x : b0 (Ok l O k) i, l ^ k • x = 0 := fun x =>
    Subtype.ext (by rw [Submodule.coe_smul_of_tower]; exact hAm x.1)
  have hmem : ∀ s (x : b0 (Ok l O k) i), ρ s x.1 ∈ b0 (Ok l O k) i := fun s x => by
    obtain ⟨hx1, hx2⟩ := x.2
    refine ⟨?_, ?_⟩
    · rw [hρ]; exact (hcj s x.1 hx1).1
    · rw [hρ, (hcj s x.1 hx1).2.1, (hcj s x.1 hx1).2.1]; exact hx2
  let f : D → (b0 (Ok l O k) i →+ b0 (Ok l O k) i) := fun s =>
    { toFun := fun x => ⟨ρ s x.1, hmem s x⟩
      map_zero' := Subtype.ext (map_zero (ρ s))
      map_add' := fun x y => Subtype.ext (map_add (ρ s) x.1 y.1) }
  let q : Fin 2 → Fin 3 := fun j => if i = 0 then j.succ else j.castSucc
  let p : Fin 2 → (b0 (Ok l O k) i →+ Ok l O k) := fun j => ent (Ok l O k) i (q j) (q j)
  refine le_trans (lower_triangular_absorbs_torsion l D I ε d k hk hLE hI (Ok l O k) (b0 (Ok l O k) i) (hkill k) hN
      { toFun := fun s => (f s).toIntLinearMap
        map_one' := LinearMap.ext fun x => Subtype.ext (by
          show ρ 1 x.1 = x.1
          rw [map_one]; rfl)
        map_mul' := fun s s' => LinearMap.ext fun x => Subtype.ext (by
          show ρ (s * s') x.1 = ρ s (ρ s' x.1)
          rw [map_mul]; rfl) }
      ?_ (card_borel_torsion_lower_bound _ i) (ent _ i i.castSucc i.succ) (ent_surj _ i) ?_ p ?_).2 ?_
  · refine Subgroup.isOpen_mono (fun s hs => ?_) hker
    rw [MonoidHom.mem_ker] at hs ⊢
    exact LinearMap.ext fun x => Subtype.ext (by
      show ρ s x.1 = x.1
      rw [hs]; rfl)
  · intro s x
    obtain ⟨hx1, hx2⟩ := x.2
    show ρ s x.1 i.castSucc i.succ = _ • x.1 i.castSucc i.succ
    rw [hρ, (hcj s x.1 hx1).2.2 i, hx2, sub_self, smul_zero, sub_zero, ← hsmul k,
      hU.1 s, mul_assoc, (hinv s).2 i.succ, mul_one]
  · intro j s x
    show ρ s x.1 (q j) (q j) = x.1 (q j) (q j)
    rw [hρ, (hcj s x.1 x.2.1).2.1]
  · refine Set.ncard_le_ncard_of_injOn (fun z s => (z s).1) ?_ ?_ ?_
    · rintro z ⟨hz, hI0⟩
      refine ⟨⟨hz.1.comp _, fun s s' => ?_, fun s => (z s).2.1, fun s hs a => ?_⟩, fun s => (z s).2.2⟩
      · show (z (s * s')).1 = (z s).1 + cj k t s (z s').1
        rw [hz.2 s s', ← hρ]; rfl
      · exact key _ i (z s).1 (z s).2.2 (fun j => hI0 j s hs) a
    · intro z _ z' _ h
      funext s; exact Subtype.ext (congrFun h s)
    · exact (hLE k hk _ ρ hAm hker).1.subset (fun z hz => ⟨hz.1.1, fun s s' => by rw [hz.1.2.1, hρ]⟩)
