import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.CyclicReductionCohomology.PolZCases

open IsLocalRing Matrix Filter NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.HV UpperTheory.V.Th GlobalTheory.GalOfCusp

/- English proof (translation)
Set `g : Z →+ Y` to `f.comp Z.subtype`. Use `haveI : Finite g.range := Finite.of_surjective _ g.rangeRestrict_surjective`. Establish `hsub : S ⊆ (g.range : Set Y)` using `fun s hs => by`. Take `⟨z, hz, rfl⟩` from `hS s hs`. Conclude with `⟨⟨z, hz⟩, rfl⟩`.

Establish `hfin : (g.range : Set Y).Finite` using `Set.toFinite _`. Use `⟨hfin.subset hsub, ?_⟩` and prove the remaining obligations. Establish `h1 : S.ncard ≤ Nat.card g.range`. Rewrite using `[← SetLike.coe_sort_coe, Nat.card_coe_set_eq]`. Conclude with `Set.ncard_le_ncard hsub hfin`.

Establish `h2 : Nat.card B ≤ Nat.card g.ker` using `Nat.card_le_card_of_injective (fun b : B => (⟨⟨b.1, hB b.2⟩, hf b.1 b.2⟩ : g.ker)) fun a b e => Subtype.ext (congrArg (fun t : g.ker => t.1.1) e)`. Establish `h3 : Nat.card Z = Nat.card g.range * Nat.card g.ker`. Rewrite using `[AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup g.ker, Nat.card_congr (QuotientAddGroup.quotientKerEquivRange g).toEquiv]`. Rewrite using `[← Nat.card_coe_set_eq (Z : Set X), SetLike.coe_sort_coe, h3]`. Conclude with `Nat.mul_le_mul h1 h2`.
-/
private theorem cnt {X Y : Type} [AddCommGroup X] [AddCommGroup Y] (Z B : AddSubgroup X) [Finite Z] (hB : B ≤ Z) (f : X →+ Y)
    (hf : ∀ b ∈ B, f b = 0) (S : Set Y) (hS : ∀ s ∈ S, ∃ z ∈ Z, f z = s) :
    S.Finite ∧ S.ncard * Nat.card B ≤ (Z : Set X).ncard := by
  let g : Z →+ Y := f.comp Z.subtype
  haveI : Finite g.range := Finite.of_surjective _ g.rangeRestrict_surjective
  have hsub : S ⊆ (g.range : Set Y) := fun s hs => by
    obtain ⟨z, hz, rfl⟩ := hS s hs
    exact ⟨⟨z, hz⟩, rfl⟩
  have hfin : (g.range : Set Y).Finite := Set.toFinite _
  refine ⟨hfin.subset hsub, ?_⟩
  have h1 : S.ncard ≤ Nat.card g.range := by
    rw [← SetLike.coe_sort_coe, Nat.card_coe_set_eq]
    exact Set.ncard_le_ncard hsub hfin
  have h2 : Nat.card B ≤ Nat.card g.ker :=
    Nat.card_le_card_of_injective (fun b : B => (⟨⟨b.1, hB b.2⟩, hf b.1 b.2⟩ : g.ker))
      fun a b e => Subtype.ext (congrArg (fun t : g.ker => t.1.1) e)
  have h3 : Nat.card Z = Nat.card g.range * Nat.card g.ker := by
    rw [AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup g.ker,
      Nat.card_congr (QuotientAddGroup.quotientKerEquivRange g).toEquiv]
  rw [← Nat.card_coe_set_eq (Z : Set X), SetLike.coe_sort_coe, h3]
  exact Nat.mul_le_mul h1 h2

/- English proof (translation)
The claim follows from `Matrix.map_mul`.
-/
private theorem red_mul {O : Type} [CommRing O] [IsLocalRing O] {n : ℕ} (m : ℕ) (A B : Matrix (Fin n) (Fin n) O) :
    red m (A * B) = red m A * red m B := Matrix.map_mul

/- English proof (translation)
The claim follows from `Matrix.map_one _ (map_zero _) (map_one _)`.
-/
private theorem red_one {O : Type} [CommRing O] [IsLocalRing O] {n : ℕ} (m : ℕ) :
    red m (1 : Matrix (Fin n) (Fin n) O) = 1 := Matrix.map_one _ (map_zero _) (map_one _)

/- English proof (translation)
Introduce `l _ L G G0 h O _ _ _ _ _ n y m rep hr hLC hF`. Establish `hmul : ∀ g g', y.ρm h m (g * g') = y.ρm h m g * y.ρm h m g'` using `fun g g' => by`. Simplify using `only [Pt.ρm, map_mul, red_mul]`. Establish `hone : y.ρm h m 1 = 1` using `by simp only [Pt.ρm, map_one, red_one]`. Establish `hrep : ∀ (g : G.G₀) Z, rep g Z = y.ρm h m g * Z * y.ρm h m g⁻¹` using `fun g Z => (hr.1 g Z).trans (one_smul _ _)`.

Establish `hφ : ∀ v g, h.p₀ (G.φ v g) = G0.φ v g` using `fun v g => Subtype.ext (h.φ v g)`. Establish `hρ : ∀ v g, y.ρm h m (G.φ v g) = y.ρ0 m (G0.φ v g)` using `fun v g => by rw [Pt.ρm, hφ]; rfl`. Establish `hρ' : ∀ v g, y.ρm h m (G.φ v g)⁻¹ = y.ρ0 m (G0.φ v g)⁻¹` using `fun v g => by rw [← map_inv, hρ, map_inv]`. Set `Z : AddSubgroup (G.Γ → Mm O n m)` to `{ carrier := {z | z ∈ Zl rep ∧ (∀ v, z ∘ (G.η.ker.subtype.comp (G.φ v)) ∈ (Bl (rep.comp (G.η.ker.subtype.comp (G.φ v)) : Representation O (L.Gv v) _)).toAddSubgroup ⊔ Zbor y m v) ∧ ∀ u, ∀ g ∈ L.Ju u, z (G.φu u g) = 0} add_mem' := by`. Introduce and unpack `a b ⟨a1, a2, a3⟩ ⟨b1, b2, b3⟩`.

Conclude with `⟨add_mem a1 b1, fun v => add_mem (a2 v) (b2 v), fun u g hg => by rw [Pi.add_apply, a3 u g hg, b3 u g hg, add_zero]⟩`. Use the proof step `zero_mem' := ⟨zero_mem _, fun v => zero_mem _, fun _ _ _ => rfl⟩`. Use the proof step `neg_mem' := by`. Introduce and unpack `a ⟨a1, a2, a3⟩`. Conclude with `⟨neg_mem a1, fun v => neg_mem (a2 v), fun u g hg => by rw [Pi.neg_apply, a3 u g hg, neg_zero]⟩ }`.

Use `haveI : Finite Z := Finite.of_injective (fun z : Z => (⟨z.1, z.2.1⟩ : Zl rep)) fun a b e => Subtype.ext (congrArg (fun t : Zl rep => t.1) e)`. Set `f : (G.Γ → Mm O n m) →+ (G.G₀ → Om O m)` to `{ toFun := fun z => trFun h y m fun g => z g map_zero' := funext fun g => by simp [trFun] map_add' := fun a b => funext fun g => by simp [trFun, Matrix.add_mul] }`. Use `cnt Z (Bl rep).toAddSubgroup (fun b hb => ?_) f (fun b hb => ?_) _ ?_` and prove the remaining obligations. Take `⟨Y, hY⟩` from `(mem_Bl rep).1 hb`. Take `rfl : b = fun g => rep g Y - Y` from `funext hY`.

Use `⟨⟨(hLC Y).comp (· - Y), fun g g' => by simp only [map_mul, Module.End.mul_apply, map_sub]; abel⟩, fun v => AddSubgroup.mem_sup_left ((mem_Bl _).2 ⟨Y, fun g => rfl⟩), fun u g hg => ?_⟩` and prove the remaining obligations. Establish `e : y.ρ (h.p₀ (G.φu u g)) = 1` using `y.ine u _ ⟨g, hg, Subtype.ext (h.φu u g).symm⟩`. Establish `e1 : y.ρm h m (G.φu u g) = 1` using `by rw [Pt.ρm, mat, MonoidHom.comp_apply, e, map_one, red_one]`. Establish `e2 : y.ρm h m (G.φu u g)⁻¹ = 1`. Rewrite using `[Pt.ρm, map_inv, mat, MonoidHom.comp_apply, map_inv, e, inv_one, map_one, red_one]`.

Use `show rep (G.φu u g : G.G₀) Y - Y = 0`. Rewrite using `[hrep, e1, e2, one_mul, mul_one, sub_self]`. Take `⟨Y, hY⟩` from `(mem_Bl rep).1 hb`. Use function extensionality and compare the values at `g`. Use `show (b g * y.ρm h m g).trace = 0`.

Rewrite using `[hY, hrep, sub_mul, mul_assoc _ _ (y.ρm h m g), ← hmul, inv_mul_cancel, hone, mul_one, Matrix.trace_sub, Matrix.trace_mul_comm, sub_self]`. Introduce and unpack `_ ⟨z, ⟨z1, z2, z3, z4, z5⟩, rfl⟩`. Establish `hP : IsUnit (red m (y.P : Matrix (Fin n) (Fin n) O))` using `⟨⟨red m (y.P : Matrix (Fin n) (Fin n) O), red m ((y.P⁻¹ : GL (Fin n) O) : Matrix (Fin n) (Fin n) O), by rw [← red_mul, Units.mul_inv, red_one], by rw [← red_mul, Units.inv_mul, red_one]⟩, rfl⟩`. Take `⟨z', h1, -, h3⟩` from `(polP l G.frame O (Om O m) n _ _ _ rep hP hr).1 z z1 (fun g g' => by rw [one_smul]; exact z2 g g') (fun g => by rw [one_smul]; exact z3 g)`. Use `⟨z', ⟨h1, fun v => ?_, fun u g hg => (h3 _).trans (z4 u _ ⟨g, hg, rfl⟩)⟩, funext fun g => by show (z' g * _).trace = (z g * _).trace` and prove the remaining obligations.

Rewrite using `[h3]⟩`. Take `⟨Y, hY⟩` from `z5 v`. Establish `hc : Continuous (G.η.ker.subtype.comp (G.φ v))` using `continuous_subtype_val.comp (G.φ_cont v)`. Establish `e : z' ∘ (G.η.ker.subtype.comp (G.φ v)) = (fun g => rep (G.φ v g : G.G₀) Y - Y) + fun g => z' (G.φ v g : G.G₀) - (rep (G.φ v g : G.G₀) Y - Y)` using `funext fun g => by simp`. Rewrite using `[e]`.

Use `AddSubgroup.add_mem_sup ((mem_Bl _).2 ⟨Y, fun g => rfl⟩) ⟨?_, fun g g' => ?_, fun g => ?_⟩` and prove the remaining obligations. Conclude with `(h1.1.comp_continuous hc).sub (((hLC Y).comp_continuous hc).comp (· - Y))`. Rewrite using `[← hρ, ← hρ', ← hrep] beta_reduce`. Rewrite using `[map_mul, Subgroup.coe_mul, h1.2, map_mul, Module.End.mul_apply, map_sub, map_sub]`. Normalize the expressions using the abelian group laws.

Use `(hY g).1` as an intermediate fact. Rewrite `this` using `[dY, ← hrep]`. Simplify using `only [h3]`. Conclude with `this`.
-/
theorem UpperTheory.V.Th.selTr :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G G0 : Glob l L) (h : G.Hom G0) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (n : ℕ) (y : Pt G0.frame O n) (m : ℕ) (rep : Representation O G.Γ (Mm O n m)), IsAd0 h y m rep → LC rep → Finite (Zl rep) → (trFun h y m '' Sel h y m).Finite ∧ (trFun h y m '' Sel h y m).ncard * Nat.card (Bl rep) ≤ {z | z ∈ Zl rep ∧ (∀ v, z ∘ (G.η.ker.subtype.comp (G.φ v)) ∈ (Bl (rep.comp (G.η.ker.subtype.comp (G.φ v)) : Representation O (L.Gv v) _)).toAddSubgroup ⊔ Zbor y m v) ∧ ∀ u, ∀ g ∈ L.Ju u, z (G.φu u g) = 0}.ncard := by
  intro l _ L G G0 h O _ _ _ _ _ n y m rep hr hLC hF
  have hmul : ∀ g g', y.ρm h m (g * g') = y.ρm h m g * y.ρm h m g' := fun g g' => by
    simp only [Pt.ρm, map_mul, red_mul]
  have hone : y.ρm h m 1 = 1 := by simp only [Pt.ρm, map_one, red_one]
  have hrep : ∀ (g : G.G₀) Z, rep g Z = y.ρm h m g * Z * y.ρm h m g⁻¹ := fun g Z => (hr.1 g Z).trans (one_smul _ _)
  have hφ : ∀ v g, h.p₀ (G.φ v g) = G0.φ v g := fun v g => Subtype.ext (h.φ v g)
  have hρ : ∀ v g, y.ρm h m (G.φ v g) = y.ρ0 m (G0.φ v g) := fun v g => by rw [Pt.ρm, hφ]; rfl
  have hρ' : ∀ v g, y.ρm h m (G.φ v g)⁻¹ = y.ρ0 m (G0.φ v g)⁻¹ := fun v g => by rw [← map_inv, hρ, map_inv]
  let Z : AddSubgroup (G.Γ → Mm O n m) :=
    { carrier := {z | z ∈ Zl rep ∧ (∀ v, z ∘ (G.η.ker.subtype.comp (G.φ v)) ∈ (Bl (rep.comp (G.η.ker.subtype.comp (G.φ v)) : Representation O (L.Gv v) _)).toAddSubgroup ⊔ Zbor y m v) ∧ ∀ u, ∀ g ∈ L.Ju u, z (G.φu u g) = 0}
      add_mem' := by
        rintro a b ⟨a1, a2, a3⟩ ⟨b1, b2, b3⟩
        exact ⟨add_mem a1 b1, fun v => add_mem (a2 v) (b2 v), fun u g hg => by rw [Pi.add_apply, a3 u g hg, b3 u g hg, add_zero]⟩
      zero_mem' := ⟨zero_mem _, fun v => zero_mem _, fun _ _ _ => rfl⟩
      neg_mem' := by
        rintro a ⟨a1, a2, a3⟩
        exact ⟨neg_mem a1, fun v => neg_mem (a2 v), fun u g hg => by rw [Pi.neg_apply, a3 u g hg, neg_zero]⟩ }
  haveI : Finite Z := Finite.of_injective (fun z : Z => (⟨z.1, z.2.1⟩ : Zl rep))
    fun a b e => Subtype.ext (congrArg (fun t : Zl rep => t.1) e)
  let f : (G.Γ → Mm O n m) →+ (G.G₀ → Om O m) :=
    { toFun := fun z => trFun h y m fun g => z g
      map_zero' := funext fun g => by simp [trFun]
      map_add' := fun a b => funext fun g => by simp [trFun, Matrix.add_mul] }
  refine cnt Z (Bl rep).toAddSubgroup (fun b hb => ?_) f (fun b hb => ?_) _ ?_
  · obtain ⟨Y, hY⟩ := (mem_Bl rep).1 hb
    obtain rfl : b = fun g => rep g Y - Y := funext hY
    refine ⟨⟨(hLC Y).comp (· - Y), fun g g' => by simp only [map_mul, Module.End.mul_apply, map_sub]; abel⟩,
      fun v => AddSubgroup.mem_sup_left ((mem_Bl _).2 ⟨Y, fun g => rfl⟩), fun u g hg => ?_⟩
    have e : y.ρ (h.p₀ (G.φu u g)) = 1 := y.ine u _ ⟨g, hg, Subtype.ext (h.φu u g).symm⟩
    have e1 : y.ρm h m (G.φu u g) = 1 := by rw [Pt.ρm, mat, MonoidHom.comp_apply, e, map_one, red_one]
    have e2 : y.ρm h m (G.φu u g)⁻¹ = 1 := by
      rw [Pt.ρm, map_inv, mat, MonoidHom.comp_apply, map_inv, e, inv_one, map_one, red_one]
    show rep (G.φu u g : G.G₀) Y - Y = 0
    rw [hrep, e1, e2, one_mul, mul_one, sub_self]
  · obtain ⟨Y, hY⟩ := (mem_Bl rep).1 hb
    funext g
    show (b g * y.ρm h m g).trace = 0
    rw [hY, hrep, sub_mul, mul_assoc _ _ (y.ρm h m g), ← hmul, inv_mul_cancel, hone, mul_one, Matrix.trace_sub,
      Matrix.trace_mul_comm, sub_self]
  · rintro _ ⟨z, ⟨z1, z2, z3, z4, z5⟩, rfl⟩
    have hP : IsUnit (red m (y.P : Matrix (Fin n) (Fin n) O)) :=
      ⟨⟨red m (y.P : Matrix (Fin n) (Fin n) O), red m ((y.P⁻¹ : GL (Fin n) O) : Matrix (Fin n) (Fin n) O), by rw [← red_mul, Units.mul_inv, red_one],
        by rw [← red_mul, Units.inv_mul, red_one]⟩, rfl⟩
    obtain ⟨z', h1, -, h3⟩ := (polP l G.frame O (Om O m) n _ _ _ rep hP hr).1 z z1
      (fun g g' => by rw [one_smul]; exact z2 g g') (fun g => by rw [one_smul]; exact z3 g)
    refine ⟨z', ⟨h1, fun v => ?_, fun u g hg => (h3 _).trans (z4 u _ ⟨g, hg, rfl⟩)⟩, funext fun g => by
      show (z' g * _).trace = (z g * _).trace
      rw [h3]⟩
    obtain ⟨Y, hY⟩ := z5 v
    have hc : Continuous (G.η.ker.subtype.comp (G.φ v)) := continuous_subtype_val.comp (G.φ_cont v)
    have e : z' ∘ (G.η.ker.subtype.comp (G.φ v)) = (fun g => rep (G.φ v g : G.G₀) Y - Y) +
        fun g => z' (G.φ v g : G.G₀) - (rep (G.φ v g : G.G₀) Y - Y) := funext fun g => by simp
    rw [e]
    refine AddSubgroup.add_mem_sup ((mem_Bl _).2 ⟨Y, fun g => rfl⟩) ⟨?_, fun g g' => ?_, fun g => ?_⟩
    · exact (h1.1.comp_continuous hc).sub (((hLC Y).comp_continuous hc).comp (· - Y))
    · rw [← hρ, ← hρ', ← hrep]
      beta_reduce
      rw [map_mul, Subgroup.coe_mul, h1.2, map_mul, Module.End.mul_apply, map_sub, map_sub]
      abel
    · have := (hY g).1
      rw [dY, ← hrep] at this
      simp only [h3]
      exact this
