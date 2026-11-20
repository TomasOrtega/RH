import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.NearSplit
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.EntryMem
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.FerreroWashington

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

section SlopeTestRemainingChoices

variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} {D : Raw Ω c}

/- English proof (translation)
Use `haveI := c.dvr`. Use `haveI := c.fin`. Take `⟨-, -, hloc, -, -, he, -, hval, -⟩` from `dvrFacts l c.O`. Rewrite using `[CharP.charP_iff_prime_eq_zero (Fact.out : l.Prime)]`. Establish `hmem : ((l : ℕ) : c.O) ∈ maximalIdeal c.O`.

Rewrite using `[mem_maximalIdeal, mem_nonunits_iff]`. Introduce `hu`. Establish `h0 : IsDiscreteValuationRing.addVal c.O (l : c.O) = 0` using `(IsDiscreteValuationRing.addVal_eq_zero_iff).2 hu`. Conclude with `he (hval.trans h0)`. Use `(residue_eq_zero_iff ((l : ℕ) : c.O)).2 hmem` as an intermediate fact.

Simplify using `using this`.
-/
private theorem charP_res (c : Coef l) : CharP (ResidueField c.O) l := by
  haveI := c.dvr
  haveI := c.fin
  obtain ⟨-, -, hloc, -, -, he, -, hval, -⟩ := dvrFacts l c.O
  rw [CharP.charP_iff_prime_eq_zero (Fact.out : l.Prime)]
  have hmem : ((l : ℕ) : c.O) ∈ maximalIdeal c.O := by
    rw [mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    have h0 : IsDiscreteValuationRing.addVal c.O (l : c.O) = 0 :=
      (IsDiscreteValuationRing.addVal_eq_zero_iff).2 hu
    exact he (hval.trans h0)
  have := (residue_eq_zero_iff ((l : ℕ) : c.O)).2 hmem
  simpa using this

/- English proof (translation)
Use `haveI := charP_res c`. Use `haveI : ExpChar (ResidueField c.O) l := ExpChar.prime Fact.out`. Proceed by induction on `j with`. Consider the case `zero => simpa using h`. Consider the case `succ n ih`.

Apply `ih` to reduce the goal to its premises. Apply `frobenius_inj (ResidueField c.O) l` to reduce the goal to its premises. Simplify `h` using `[frobenius_def, pow_succ, pow_mul]`.
-/
private theorem pow_inj {x y : ResidueField c.O} (j : ℕ) (h : x ^ l ^ j = y ^ l ^ j) : x = y := by
  haveI := charP_res c
  haveI : ExpChar (ResidueField c.O) l := ExpChar.prime Fact.out
  induction j with
  | zero => simpa using h
  | succ n ih =>
    apply ih
    apply frobenius_inj (ResidueField c.O) l
    simpa [frobenius_def, pow_succ, pow_mul] using h

/- English proof (translation)
Conclude with `pow_inj j (by simpa using h)`.
-/
private theorem pow_one_inj {x : ResidueField c.O} (j : ℕ) (h : x ^ l ^ j = 1) : x = 1 := by
  exact pow_inj j (by simpa using h)

/- English proof (translation)
Rewrite using `[IntermediateField.mem_fixingSubgroup_iff]`. Conclude with `fun x hx => g.commutes ⟨x, hx⟩`.
-/
private theorem resQ_mem (F : IntermediateField ℚ Ω) (g : G F Ω) : resQ F g ∈ F.fixingSubgroup := by
  rw [IntermediateField.mem_fixingSubgroup_iff]
  exact fun x hx => g.commutes ⟨x, hx⟩

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
private theorem dec_resLe {F F' : IntermediateField ℚ Ω} (h : F ≤ F') (A : ValuationSubring Ω) (g : G F' Ω) :
    resLe h g ∈ Dec (F := F) A ↔ g ∈ Dec (F := F') A := Iff.rfl

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
private theorem ine_resLe {F F' : IntermediateField ℚ Ω} [NumberField F] [NumberField F'] (h : F ≤ F')
    (A : ValuationSubring Ω) (g : G F' Ω) :
    resLe h g ∈ Ine (F := F) A ↔ g ∈ Ine (F := F') A := Iff.rfl

variable {T T' : Tower D}

/- English proof (translation)
Take `⟨j, hj⟩` from `h.pow`. Use `⟨j, fun g => ?_⟩` and prove the remaining obligations. Establish `hm` using `hj _ (resQ_mem T.F g)`. Use `⟨IntermediateField.fixingSubgroupEquiv T'.F ⟨_, hm⟩, ?_⟩` and prove the remaining obligations. Use extensionality with `x`.

Simplify using `[resLe, IntermediateField.fixingSubgroupEquiv, map_pow]`.
-/
private theorem up (h : T.Le T') : ∃ j : ℕ, ∀ g : G T.F Ω, ∃ g' : G T'.F Ω, resLe h.le g' = g ^ l ^ j := by
  obtain ⟨j, hj⟩ := h.pow
  refine ⟨j, fun g => ?_⟩
  have hm := hj _ (resQ_mem T.F g)
  refine ⟨IntermediateField.fixingSubgroupEquiv T'.F ⟨_, hm⟩, ?_⟩
  ext x
  simp [resLe, IntermediateField.fixingSubgroupEquiv, map_pow]

/- English proof (translation)
Simplify using `only [Tower.rb, Tower.fr, Fr.rt, h.pr]`. Both sides reduce to the same expression.
-/
private theorem rb_resLe (h : T.Le T') (w : ℤ × ℤ) (g : G T'.F Ω) : T'.rb w g = T.rb w (resLe h.le g) := by
  simp only [Tower.rb, Tower.fr, Fr.rt, h.pr]
  rfl

/- English proof (translation)
Simplify using `only [Tower.rb, map_pow, Units.val_pow_eq_pow_val]`.
-/
private theorem rb_pow (w : ℤ × ℤ) (g : G T.F Ω) (n : ℕ) : T.rb w (g ^ n) = T.rb w g ^ n := by
  simp only [Tower.rb, map_pow, Units.val_pow_eq_pow_val]

/- English proof (translation)
Simplify using `only [Raw.bar, map_pow, Units.val_pow_eq_pow_val]`.
-/
private theorem bar_pow (γ : G ℚ Ω →* c.Oˣ) (g : G ℚ Ω) (n : ℕ) : Raw.bar γ (g ^ n) = Raw.bar γ g ^ n := by
  simp only [Raw.bar, map_pow, Units.val_pow_eq_pow_val]

/- English proof (translation)
Simplify using `only [Tower.GalL, Subgroup.mem_comap, h.K]`. Both sides reduce to the same expression.
-/
private theorem galL_resLe (h : T.Le T') (g : G T'.F Ω) : resLe h.le g ∈ T.GalL ↔ g ∈ T'.GalL := by
  simp only [Tower.GalL, Subgroup.mem_comap, h.K]
  rfl

/- English proof (translation)
Take `⟨k, hk⟩` from `up h`. Establish `L : ∀ u : (ResidueField c.O)ˣ, u ^ l ^ k = 1 → u = 1` using `fun u hu => Units.ext (pow_one_inj k (by rw [← Units.val_pow_eq_pow_val, hu, Units.val_one]))`. Set `φ : Fin 4 → T.GalL →* (ResidueField c.O)ˣ` to `fun m => (Units.map (residue c.O).toMonoidHom).comp ((chi D T.pr m).comp ((resQ T.F).comp T.GalL.subtype))`. Set `φ' : Fin 4 → T'.GalL →* (ResidueField c.O)ˣ` to `fun m => (Units.map (residue c.O).toMonoidHom).comp ((chi D T.pr m).comp ((resQ T'.F).comp T'.GalL.subtype))`. Establish `hφ : ∀ m (g : T'.GalL), φ m ⟨resLe h.le g, (galL_resLe h g).2 g.2⟩ = φ' m g` using `fun _ _ => rfl`.

Establish `hperm' : ∀ i, ∃ j, ∀ g : T'.GalL, η g * φ' i g = φ' j g`. Introduce `i`. Take `⟨j, hj⟩` from `hperm i`. Use `⟨j, fun g => Units.ext ?_⟩` and prove the remaining obligations. Establish `hj'` using `hj g`.

Rewrite `hj'` using `[h.pr]`. Simplify `hj'` using `[φ', Raw.bar]`. Establish `lift : ∀ g : T.GalL, ∃ g' : T'.GalL, ∀ m, φ m g ^ l ^ k = φ' m g' ∧ (D.om (resQ T.F g) = 1 → D.om (resQ T'.F g') = 1)`. Introduce `g`. Take `⟨g', hg'⟩` from `hk g`.

Establish `hm : g' ∈ T'.GalL` using `(galL_resLe h g').1 (by rw [hg']; exact pow_mem g.2 _)`. Use `⟨⟨g', hm⟩, fun m => ⟨?_, fun h1 => ?_⟩⟩` and prove the remaining obligations. Rewrite using `[← map_pow, ← hφ]`. Use `congr 1`. Conclude with `Subtype.ext (by simp [hg'])`.

Use `show D.om (resQ T.F (resLe h.le g')) = 1`. Rewrite using `[hg', map_pow, map_pow, h1, one_pow]`. Take `⟨j, hj⟩` from `hperm' 0`. Establish `hη : ∀ g : T'.GalL, η g = φ' j g / φ' 0 g` using `fun g => eq_div_iff_mul_eq'.2 (hj g)`. Set `η₀ : T.GalL →* (ResidueField c.O)ˣ` to `φ j / φ 0`.

Establish `hη₀ : ∀ g, η₀ g = φ j g / φ 0 g` using `fun _ => rfl`. Establish `C : ∀ (g : T.GalL) (g' : T'.GalL), (∀ m, φ m g ^ l ^ k = φ' m g') → η₀ g ^ l ^ k = η g'`. Introduce `g g' hm`. Rewrite using `[hη g', ← hm j, ← hm 0, hη₀, div_pow]`. Establish `h0 : η₀ = 1`.

Use `ho.g3' η₀ ?_ ?_ ?_` and prove the remaining obligations. Use `MonoidHom.ext fun g => ?_` and prove the remaining obligations. Take `⟨g', hg'⟩` from `lift g`. Rewrite using `[MonoidHom.one_apply, MonoidHom.pow_apply]`. Apply `L` to reduce the goal to its premises.

Rewrite using `[← pow_mul, mul_comm, pow_mul, C g g' (fun m => (hg' m).1), ← MonoidHom.pow_apply, h2, MonoidHom.one_apply]`. Introduce `g hg`. Take `⟨g', hg'⟩` from `lift g`. Apply `L` to reduce the goal to its premises. Rewrite using `[C g g' (fun m => (hg' m).1)]`.

Conclude with `hom g' ((hg' 0).2 hg)`. Introduce `i`. Take `⟨i', hi'⟩` from `hperm' i`. Use `⟨i', fun g => ?_⟩` and prove the remaining obligations. Establish `key : η₀ g * φ i g = φ i' g`.

Take `⟨g', hg'⟩` from `lift g`. Establish `hu : η₀ g * φ i g / φ i' g = 1`. Apply `L` to reduce the goal to its premises. Rewrite using `[div_pow, mul_pow, C g g' (fun m => (hg' m).1), (hg' i).1, (hg' i').1, hi' g', div_self']`. Conclude with `div_eq_one.1 hu`.

Use `congrArg Units.val key` as an intermediate fact. Simplify `this` using `[φ, Raw.bar]`. Use `MonoidHom.ext fun g => ?_` and prove the remaining obligations. Rewrite using `[hη g, MonoidHom.one_apply, div_eq_one, ← hφ, ← hφ]`. Use `congrArg (fun f : T.GalL →* (ResidueField c.O)ˣ => f ⟨resLe h.le g, (galL_resLe h g).2 g.2⟩) h0` as an intermediate fact.

Simplify using `only [hη₀, MonoidHom.one_apply, div_eq_one] at this`. Conclude with `this`.
-/
private theorem g3'_up (hl : l ≠ 2) (h : T.Le T') (ho : T.Ok) (η : T'.GalL →* (ResidueField c.O)ˣ) (h2 : η ^ 2 = 1)
    (hom : ∀ g : T'.GalL, D.om (resQ T'.F g) = 1 → η g = 1)
    (hperm : ∀ i, ∃ j, ∀ g : T'.GalL, η g * Raw.bar (chi D T'.pr i) (resQ T'.F g) =
      Raw.bar (chi D T'.pr j) (resQ T'.F g)) : η = 1 := by
  obtain ⟨k, hk⟩ := up h
  have L : ∀ u : (ResidueField c.O)ˣ, u ^ l ^ k = 1 → u = 1 := fun u hu =>
    Units.ext (pow_one_inj k (by rw [← Units.val_pow_eq_pow_val, hu, Units.val_one]))
  let φ : Fin 4 → T.GalL →* (ResidueField c.O)ˣ := fun m =>
    (Units.map (residue c.O).toMonoidHom).comp ((chi D T.pr m).comp ((resQ T.F).comp T.GalL.subtype))
  let φ' : Fin 4 → T'.GalL →* (ResidueField c.O)ˣ := fun m =>
    (Units.map (residue c.O).toMonoidHom).comp ((chi D T.pr m).comp ((resQ T'.F).comp T'.GalL.subtype))
  have hφ : ∀ m (g : T'.GalL), φ m ⟨resLe h.le g, (galL_resLe h g).2 g.2⟩ = φ' m g := fun _ _ => rfl
  have hperm' : ∀ i, ∃ j, ∀ g : T'.GalL, η g * φ' i g = φ' j g := by
    intro i
    obtain ⟨j, hj⟩ := hperm i
    refine ⟨j, fun g => Units.ext ?_⟩
    have hj' := hj g
    rw [h.pr] at hj'
    simpa [φ', Raw.bar] using hj'
  have lift : ∀ g : T.GalL, ∃ g' : T'.GalL, ∀ m, φ m g ^ l ^ k = φ' m g' ∧
      (D.om (resQ T.F g) = 1 → D.om (resQ T'.F g') = 1) := by
    intro g
    obtain ⟨g', hg'⟩ := hk g
    have hm : g' ∈ T'.GalL := (galL_resLe h g').1 (by rw [hg']; exact pow_mem g.2 _)
    refine ⟨⟨g', hm⟩, fun m => ⟨?_, fun h1 => ?_⟩⟩
    · rw [← map_pow, ← hφ]
      congr 1
      exact Subtype.ext (by simp [hg'])
    · show D.om (resQ T.F (resLe h.le g')) = 1
      rw [hg', map_pow, map_pow, h1, one_pow]
  obtain ⟨j, hj⟩ := hperm' 0
  have hη : ∀ g : T'.GalL, η g = φ' j g / φ' 0 g := fun g => eq_div_iff_mul_eq'.2 (hj g)
  let η₀ : T.GalL →* (ResidueField c.O)ˣ := φ j / φ 0
  have hη₀ : ∀ g, η₀ g = φ j g / φ 0 g := fun _ => rfl
  have C : ∀ (g : T.GalL) (g' : T'.GalL), (∀ m, φ m g ^ l ^ k = φ' m g') → η₀ g ^ l ^ k = η g' := by
    intro g g' hm
    rw [hη g', ← hm j, ← hm 0, hη₀, div_pow]
  have h0 : η₀ = 1 := by
    refine ho.g3' η₀ ?_ ?_ ?_
    · refine MonoidHom.ext fun g => ?_
      obtain ⟨g', hg'⟩ := lift g
      rw [MonoidHom.one_apply, MonoidHom.pow_apply]
      apply L
      rw [← pow_mul, mul_comm, pow_mul, C g g' (fun m => (hg' m).1), ← MonoidHom.pow_apply, h2,
        MonoidHom.one_apply]
    · intro g hg
      obtain ⟨g', hg'⟩ := lift g
      apply L
      rw [C g g' (fun m => (hg' m).1)]
      exact hom g' ((hg' 0).2 hg)
    · intro i
      obtain ⟨i', hi'⟩ := hperm' i
      refine ⟨i', fun g => ?_⟩
      have key : η₀ g * φ i g = φ i' g := by
        obtain ⟨g', hg'⟩ := lift g
        have hu : η₀ g * φ i g / φ i' g = 1 := by
          apply L
          rw [div_pow, mul_pow, C g g' (fun m => (hg' m).1), (hg' i).1, (hg' i').1, hi' g', div_self']
        exact div_eq_one.1 hu
      have := congrArg Units.val key
      simpa [φ, Raw.bar] using this
  refine MonoidHom.ext fun g => ?_
  rw [hη g, MonoidHom.one_apply, div_eq_one, ← hφ, ← hφ]
  have := congrArg (fun f : T.GalL →* (ResidueField c.O)ˣ => f ⟨resLe h.le g, (galL_resLe h g).2 g.2⟩) h0
  simp only [hη₀, MonoidHom.one_apply, div_eq_one] at this
  exact this

/- English proof (translation)
Take `⟨k, hk⟩` from `up h`. Establish `L1 : ∀ x : ResidueField c.O, x ^ l ^ k = 1 → x = 1` using `fun x hx => pow_one_inj k hx`. Establish `liftL : ∀ g ∈ T.GalL, ∃ g' ∈ T'.GalL, resLe h.le g' = g ^ l ^ k` using `fun g hg => by`. Take `⟨g', hg'⟩` from `hk g`. Conclude with `⟨g', (galL_resLe h g').1 (by rw [hg']; exact pow_mem hg _), hg'⟩`.

Use `{ lab := ?_, even := ?_, unr := ?_, split := ?_, g2 := ?_, g3 := ?_, g3' := ?_, ord := ?_, kb := ?_, kc := ?_, ineL := ?_, dist := ?_, locL := ?_ }` and prove the remaining obligations. Rewrite using `[h.pr]`. Conclude with `ho.lab`. Take `⟨n, hn⟩` from `IntermediateField.finrank_dvd_of_le_right h.le show Even (Module.finrank ℚ T'.F)`. Rewrite using `[hn]`.

Conclude with `(show Even (Module.finrank ℚ T.F) from ho.even).mul_right n`. Introduce `A g hg`. Conclude with `(galL_resLe h g).1 (ho.unr A ((ine_resLe h.le A g).2 hg))`. Introduce `p hp A hA`. Rewrite using `[h.K]`.

Conclude with `ho.split p hp A hA`. Introduce `w`. Take `⟨g, hg, hne⟩` from `ho.g2 w`. Take `⟨g', hm, hg'⟩` from `liftL g hg`. Use `⟨g', hm, fun heq => hne (pow_inj k ?_)⟩` and prove the remaining obligations.

Rewrite using `[← rb_pow, ← bar_pow, ← map_pow (resQ T.F), ← hg', ← rb_resLe h]`. Conclude with `heq`. Introduce `w hw`. Take `⟨g, hg, hne⟩` from `ho.g3 w hw`. Take `⟨g', hm, hg'⟩` from `liftL g hg`.

Conclude with `⟨g', hm, fun heq => hne (L1 _ (by rw [← rb_pow, ← hg', ← rb_resLe h]; exact heq))⟩`. Conclude with `fun η h2 hom hperm => g3'_up hl h ho η h2 hom hperm`. Take `⟨w, hw, hord⟩` from `ho.ord`. Use `⟨w, hw, fun n hn0 hn4 => ?_⟩` and prove the remaining obligations. Take `⟨g, hg, hne⟩` from `hord n hn0 hn4`.

Take `⟨g', hm, hg'⟩` from `liftL g hg`. Use `⟨g', hm, fun heq => hne (L1 _ ?_)⟩` and prove the remaining obligations. Rewrite using `[← pow_mul, mul_comm, pow_mul, ← rb_pow, ← hg', ← rb_resLe h]`. Conclude with `heq`. Introduce `A hA g hg h1`.

Conclude with `ho.kb A hA (resLe h.le g) ((ine_resLe h.le A g).2 hg) h1`. Take `⟨m, hm, hψ⟩` from `ho.kc`. Conclude with `⟨m, hm, fun g hg => hψ (resLe h.le g) hg⟩`. Introduce `A hA g hg`. Conclude with `ho.ineL A hA (resLe h.le g) ((ine_resLe h.le A g).2 hg)`.

Introduce `i j hij heq`. Apply `ho.dist i j hij` to reduce the goal to its premises. Take `⟨k', hk'⟩` from `h.g0`. Apply `pow_inj k'` to reduce the goal to its premises. Rewrite using `[← bar_pow, ← bar_pow, ← hk']`.

Rewrite `heq` using `[h.pr]`. Conclude with `heq`. Introduce `A hA`. Break down `ho.locL A hA with ⟨g, hg, hne⟩ | ⟨g, hg, h1, h2, h3⟩` into its components or cases. Take `⟨g', hg'⟩` from `hk g left`.

Use `⟨g', (ine_resLe h.le A g').1 (by rw [hg']; exact pow_mem hg _), fun heq => hne (L1 _ ?_)⟩` and prove the remaining obligations. Rewrite using `[← bar_pow, ← map_pow (resQ T.F), ← hg']`. Conclude with `heq`. Take `⟨g', hg'⟩` from `hk g right`. Use `⟨g', (dec_resLe h.le A g').1 (by rw [hg']; exact pow_mem hg _), ?_, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[show resQ T'.F g' = resQ T.F (resLe h.le g') from rfl, hg', map_pow, bar_pow, h1, one_pow]`. Rewrite using `[rb_resLe h, hg', rb_pow, h2, one_pow]`. Conclude with `fun heq => h3 (L1 _ (by rw [← rb_pow, ← hg', ← rb_resLe h]; exact heq))`.
-/
private theorem ok_up (hl : l ≠ 2) (h : T.Le T') (ho : T.Ok) : T'.Ok := by
  obtain ⟨k, hk⟩ := up h
  have L1 : ∀ x : ResidueField c.O, x ^ l ^ k = 1 → x = 1 := fun x hx => pow_one_inj k hx
  have liftL : ∀ g ∈ T.GalL, ∃ g' ∈ T'.GalL, resLe h.le g' = g ^ l ^ k := fun g hg => by
    obtain ⟨g', hg'⟩ := hk g
    exact ⟨g', (galL_resLe h g').1 (by rw [hg']; exact pow_mem hg _), hg'⟩
  refine
    { lab := ?_, even := ?_, unr := ?_, split := ?_, g2 := ?_, g3 := ?_, g3' := ?_, ord := ?_,
      kb := ?_, kc := ?_, ineL := ?_, dist := ?_, locL := ?_ }
  · rw [h.pr]
    exact ho.lab
  · obtain ⟨n, hn⟩ := IntermediateField.finrank_dvd_of_le_right h.le
    show Even (Module.finrank ℚ T'.F)
    rw [hn]
    exact (show Even (Module.finrank ℚ T.F) from ho.even).mul_right n
  · intro A g hg
    exact (galL_resLe h g).1 (ho.unr A ((ine_resLe h.le A g).2 hg))
  · intro p hp A hA
    rw [h.K]
    exact ho.split p hp A hA
  · intro w
    obtain ⟨g, hg, hne⟩ := ho.g2 w
    obtain ⟨g', hm, hg'⟩ := liftL g hg
    refine ⟨g', hm, fun heq => hne (pow_inj k ?_)⟩
    rw [← rb_pow, ← bar_pow, ← map_pow (resQ T.F), ← hg', ← rb_resLe h]
    exact heq
  · intro w hw
    obtain ⟨g, hg, hne⟩ := ho.g3 w hw
    obtain ⟨g', hm, hg'⟩ := liftL g hg
    exact ⟨g', hm, fun heq => hne (L1 _ (by rw [← rb_pow, ← hg', ← rb_resLe h]; exact heq))⟩
  · exact fun η h2 hom hperm => g3'_up hl h ho η h2 hom hperm
  · obtain ⟨w, hw, hord⟩ := ho.ord
    refine ⟨w, hw, fun n hn0 hn4 => ?_⟩
    obtain ⟨g, hg, hne⟩ := hord n hn0 hn4
    obtain ⟨g', hm, hg'⟩ := liftL g hg
    refine ⟨g', hm, fun heq => hne (L1 _ ?_)⟩
    rw [← pow_mul, mul_comm, pow_mul, ← rb_pow, ← hg', ← rb_resLe h]
    exact heq
  · intro A hA g hg h1
    exact ho.kb A hA (resLe h.le g) ((ine_resLe h.le A g).2 hg) h1
  · obtain ⟨m, hm, hψ⟩ := ho.kc
    exact ⟨m, hm, fun g hg => hψ (resLe h.le g) hg⟩
  · intro A hA g hg
    exact ho.ineL A hA (resLe h.le g) ((ine_resLe h.le A g).2 hg)
  · intro i j hij heq
    apply ho.dist i j hij
    obtain ⟨k', hk'⟩ := h.g0
    apply pow_inj k'
    rw [← bar_pow, ← bar_pow, ← hk']
    rw [h.pr] at heq
    exact heq
  · intro A hA
    rcases ho.locL A hA with ⟨g, hg, hne⟩ | ⟨g, hg, h1, h2, h3⟩
    · obtain ⟨g', hg'⟩ := hk g
      left
      refine ⟨g', (ine_resLe h.le A g').1 (by rw [hg']; exact pow_mem hg _), fun heq => hne (L1 _ ?_)⟩
      rw [← bar_pow, ← map_pow (resQ T.F), ← hg']
      exact heq
    · obtain ⟨g', hg'⟩ := hk g
      right
      refine ⟨g', (dec_resLe h.le A g').1 (by rw [hg']; exact pow_mem hg _), ?_, ?_, ?_⟩
      · rw [show resQ T'.F g' = resQ T.F (resLe h.le g') from rfl, hg', map_pow, bar_pow, h1, one_pow]
      · rw [rb_resLe h, hg', rb_pow, h2, one_pow]
      · exact fun heq => h3 (L1 _ (by rw [← rb_pow, ← hg', ← rb_resLe h]; exact heq))

/- English proof (translation)
Take `⟨j, hj⟩` from `up h`. Use `⟨fun g => ?_, fun A g hg => ?_, fun A hA g hg => ?_, ?_, ht.ord, ht.xi, fun A hA => ?_, fun A hA => ?_⟩` and prove the remaining obligations. Rewrite using `[rb_resLe h]`. Conclude with `ht.sq _`. Rewrite using `[rb_resLe h]`.

Conclude with `ht.unr A _ hg`. Rewrite using `[rb_resLe h]`. Conclude with `ht.atL A hA _ hg`. Take `⟨k₀, h1, h2, h3, h4⟩` from `ht.quad`. Use `⟨k₀, h1, h2, h3, fun g => ?_⟩` and prove the remaining obligations.

Rewrite using `[rb_resLe h]`. Conclude with `h4 _`. Take `⟨g, hg, hne⟩` from `ht.bigL A hA`. Take `⟨g', hg'⟩` from `hj g`. Use `⟨g', (dec_resLe h.le A g').1 (hg' ▸ pow_mem hg _), fun he => hne (pow_one_inj j ?_)⟩` and prove the remaining obligations.

Rewrite `he` using `[rb_resLe h, hg', rb_pow, pow_right_comm]`. Then use the resulting hypothesis. Take `⟨g, hg, hne⟩` from `ht.big2 A hA`. Take `⟨g', hg'⟩` from `hj g`. Use `⟨g', (ine_resLe h.le A g').1 (hg' ▸ pow_mem hg _), fun he => hne (pow_one_inj j ?_)⟩` and prove the remaining obligations. Rewrite `he` using `[rb_resLe h, hg', rb_pow, pow_right_comm]`. Then use the resulting hypothesis.
-/
private theorem two_up (h : T.Le T') (ht : T.Two) : T'.Two := by
  obtain ⟨j, hj⟩ := up h
  refine ⟨fun g => ?_, fun A g hg => ?_, fun A hA g hg => ?_, ?_, ht.ord, ht.xi, fun A hA => ?_, fun A hA => ?_⟩
  · rw [rb_resLe h]
    exact ht.sq _
  · rw [rb_resLe h]
    exact ht.unr A _ hg
  · rw [rb_resLe h]
    exact ht.atL A hA _ hg
  · obtain ⟨k₀, h1, h2, h3, h4⟩ := ht.quad
    refine ⟨k₀, h1, h2, h3, fun g => ?_⟩
    rw [rb_resLe h]
    exact h4 _
  · obtain ⟨g, hg, hne⟩ := ht.bigL A hA
    obtain ⟨g', hg'⟩ := hj g
    refine ⟨g', (dec_resLe h.le A g').1 (hg' ▸ pow_mem hg _), fun he => hne (pow_one_inj j ?_)⟩
    rwa [rb_resLe h, hg', rb_pow, pow_right_comm] at he
  · obtain ⟨g, hg, hne⟩ := ht.big2 A hA
    obtain ⟨g', hg'⟩ := hj g
    refine ⟨g', (ine_resLe h.le A g').1 (hg' ▸ pow_mem hg _), fun he => hne (pow_one_inj j ?_)⟩
    rwa [rb_resLe h, hg', rb_pow, pow_right_comm] at he

/- English proof (translation)
Assemble the required witnesses or components as `⟨ht.five, ht.sb, ht.psi, fun g => by rw [rb_resLe h, rb_resLe h]; exact ht.sq _⟩`.
-/
private theorem three_up (h : T.Le T') (ht : T.Three) : T'.Three :=
  ⟨ht.five, ht.sb, ht.psi, fun g => by rw [rb_resLe h, rb_resLe h]; exact ht.sq _⟩

end SlopeTestRemainingChoices

/- English proof (translation)
Introduce `Ω _ _ _ l _ c D hD T T' h`. Use `⟨ok_up hD.l_odd h, two_up h, three_up h, ?_, ?_, ⟨rfl, rfl, le_rfl, ⟨0, fun g hg => by simpa using hg⟩, ⟨0, by simp⟩⟩, fun T'' h' => ⟨h'.pr.trans h.pr, h'.K.trans h.K, h.le.trans h'.le, ?_, ?_⟩⟩` and prove the remaining obligations. Introduce and unpack `⟨m, hm, hk⟩`. Conclude with `⟨m, hm, fun g => hk (resLe h.le g)⟩`. Introduce and unpack `⟨ho, hc⟩`.

Conclude with `⟨ok_up hD.l_odd h ho, hc.imp (fun a => ⟨a.1, two_up h a.2⟩) fun a => ⟨a.1, a.2.five, a.2.sb, a.2.psi⟩⟩`. Take `⟨j, hj⟩` from `h.pow`. Take `⟨k, hk⟩` from `h'.pow`. Conclude with `⟨j + k, fun g hg => by rw [pow_add, pow_mul]; exact hk _ (hj g hg)⟩`. Take `⟨j, hj⟩` from `h.g0`.

Take `⟨k, hk⟩` from `h'.g0`. Conclude with `⟨j + k, by rw [hk, hj, pow_add, pow_mul]⟩`.
-/
theorem UpperTheory.V.Ws.leFit :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ T T' : Tower D, T.Le T' → (T.Ok → T'.Ok) ∧ (T.Two → T'.Two) ∧ (T.Three → T'.Three) ∧ (T.Deep → T'.Deep) ∧ (T.Fit → T'.Fit) ∧
      T.Le T ∧ ∀ T'' : Tower D, T'.Le T'' → T.Le T'' := by
  intro Ω _ _ _ l _ c D hD T T' h
  refine ⟨ok_up hD.l_odd h, two_up h, three_up h, ?_, ?_, ⟨rfl, rfl, le_rfl, ⟨0, fun g hg => by simpa using hg⟩, ⟨0, by simp⟩⟩,
    fun T'' h' => ⟨h'.pr.trans h.pr, h'.K.trans h.K, h.le.trans h'.le, ?_, ?_⟩⟩
  · rintro ⟨m, hm, hk⟩
    exact ⟨m, hm, fun g => hk (resLe h.le g)⟩
  · rintro ⟨ho, hc⟩
    exact ⟨ok_up hD.l_odd h ho, hc.imp (fun a => ⟨a.1, two_up h a.2⟩) fun a => ⟨a.1, a.2.five, a.2.sb, a.2.psi⟩⟩
  · obtain ⟨j, hj⟩ := h.pow
    obtain ⟨k, hk⟩ := h'.pow
    exact ⟨j + k, fun g hg => by rw [pow_add, pow_mul]; exact hk _ (hj g hg)⟩
  · obtain ⟨j, hj⟩ := h.g0
    obtain ⟨k, hk⟩ := h'.g0
    exact ⟨j + k, by rw [hk, hj, pow_add, pow_mul]⟩
