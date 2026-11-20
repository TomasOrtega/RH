import Development.EtaleCohomology.EtaleSheaves.SHTensorPf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC

namespace LateralTheory.E.LocTensorPf

/- English proof (translation)
Establish `hJ : ∀ M : Ideal Z, M.IsMaximal → Ideal.map u (IsLocalRing.maximalIdeal X) ⊔ Ideal.map v (IsLocalRing.maximalIdeal B) ≤ M`. Introduce `M hMm`. Take `⟨h1, h2⟩` from `hM M hMm`. Conclude with `sup_le (Ideal.map_le_iff_le_comap.mpr h1) (Ideal.map_le_iff_le_comap.mpr h2)`. Use `IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun z => ?_` and prove the remaining obligations.

Take `⟨N, hN, y, hy⟩` from `hF z`. Distinguish the cases in `hyu : IsUnit y`. Use `left`. Assume the negation of the conclusion as `hz`. Take `⟨M, hMm, hzM⟩` from `Ideal.exists_le_maximal (Ideal.span {z}) (by`.

Rewrite using `[Ne, Ideal.span_singleton_eq_top])` and apply the resulting hypothesis. Establish `hzM' : z ∈ M` using `hzM (Ideal.mem_span_singleton_self z)`. Establish `h1 : z ^ N - u y ∈ M` using `hJ M hMm hy`. Establish `h2 : z ^ N ∈ M` using `M.pow_mem_of_mem hzM' N hN`. Establish `h3 : u y ∈ M`.

Use `M.sub_mem h2 h1` as an intermediate fact. Simplify using `using this`. Conclude with `hMm.ne_top (M.eq_top_of_isUnit_mem h3 (hyu.map u))`. Use `right`. Assume the negation of the conclusion as `hz`.

Take `⟨M, hMm, hzM⟩` from `Ideal.exists_le_maximal (Ideal.span {1 - z}) (by`. Rewrite using `[Ne, Ideal.span_singleton_eq_top])` and apply the resulting hypothesis. Establish `hzM' : 1 - z ∈ M` using `hzM (Ideal.mem_span_singleton_self _)`. Establish `hyM : u y ∈ M`. Establish `: y ∈ IsLocalRing.maximalIdeal X` using `hyu`.

Conclude with `(hM M hMm).1 this`. Establish `h2 : z ^ N ∈ M`. Use `M.add_mem (hJ M hMm hy) hyM` as an intermediate fact. Simplify using `using this`. Establish `hz' : z ∈ M` using `hMm.isPrime.mem_of_pow_mem N h2`.

Conclude with `hMm.ne_top ((Ideal.eq_top_iff_one M).mpr (by simpa using M.add_mem hzM' hz'))`.
-/
theorem isLocalRing_of_maximal_over_and_power_in_range (Z X B : Type) [CommRing Z] [CommRing X] [CommRing B] [IsLocalRing X] [IsLocalRing B] [Nontrivial Z]
    (u : X →+* Z) (v : B →+* Z)
    (hM : ∀ M : Ideal Z, M.IsMaximal → IsLocalRing.maximalIdeal X ≤ M.comap u ∧ IsLocalRing.maximalIdeal B ≤ M.comap v)
    (hF : ∀ z : Z, ∃ N : ℕ, 0 < N ∧ ∃ y : X,
      z ^ N - u y ∈ Ideal.map u (IsLocalRing.maximalIdeal X) ⊔ Ideal.map v (IsLocalRing.maximalIdeal B)) :
    IsLocalRing Z := by
  have hJ : ∀ M : Ideal Z, M.IsMaximal →
      Ideal.map u (IsLocalRing.maximalIdeal X) ⊔ Ideal.map v (IsLocalRing.maximalIdeal B) ≤ M := by
    intro M hMm
    obtain ⟨h1, h2⟩ := hM M hMm
    exact sup_le (Ideal.map_le_iff_le_comap.mpr h1) (Ideal.map_le_iff_le_comap.mpr h2)
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun z => ?_
  obtain ⟨N, hN, y, hy⟩ := hF z
  by_cases hyu : IsUnit y
  · left
    by_contra hz
    obtain ⟨M, hMm, hzM⟩ := Ideal.exists_le_maximal (Ideal.span {z}) (by
      rwa [Ne, Ideal.span_singleton_eq_top])
    have hzM' : z ∈ M := hzM (Ideal.mem_span_singleton_self z)
    have h1 : z ^ N - u y ∈ M := hJ M hMm hy
    have h2 : z ^ N ∈ M := M.pow_mem_of_mem hzM' N hN
    have h3 : u y ∈ M := by
      have := M.sub_mem h2 h1; simpa using this
    exact hMm.ne_top (M.eq_top_of_isUnit_mem h3 (hyu.map u))
  · right
    by_contra hz
    obtain ⟨M, hMm, hzM⟩ := Ideal.exists_le_maximal (Ideal.span {1 - z}) (by
      rwa [Ne, Ideal.span_singleton_eq_top])
    have hzM' : 1 - z ∈ M := hzM (Ideal.mem_span_singleton_self _)
    have hyM : u y ∈ M := by
      have : y ∈ IsLocalRing.maximalIdeal X := hyu
      exact (hM M hMm).1 this
    have h2 : z ^ N ∈ M := by
      have := M.add_mem (hJ M hMm hy) hyM; simpa using this
    have hz' : z ∈ M := hMm.isPrime.mem_of_pow_mem N h2
    exact hMm.ne_top ((Ideal.eq_top_iff_one M).mpr (by simpa using M.add_mem hzM' hz'))

open IsLocalRing in
/- English proof (translation)
Establish `hu : u.hom.IsIntegral` using `LateralTheory.E.SHTensorPf.intPush hp hb`. Establish `hX : (M.comap u.hom).IsMaximal`. Set `_` to `u.hom.toAlgebra`. Establish `: Algebra.IsIntegral X Z` using `⟨hu⟩`. Conclude with `Ideal.isMaximal_comap_of_isIntegral_of_isMaximal M`.

Establish `hXe : M.comap u.hom = maximalIdeal X` using `IsLocalRing.eq_maximalIdeal hX`. Establish `hw : u.hom.comp x.hom = v.hom.comp b.hom`. Use `congrArg CommRingCat.Hom.hom hp.w` as an intermediate fact. Simplify using `using this`. Establish `hA : ((M.comap v.hom).comap b.hom) = maximalIdeal A`.

Rewrite using `[Ideal.comap_comap, ← hw, ← Ideal.comap_comap, hXe]`. Use extensionality with `a`. Simplify using `only [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]`. Conclude with `not_congr (isUnit_map_iff x.hom a)`. Establish `hB : (M.comap v.hom).IsMaximal`.

Set `_` to `b.hom.toAlgebra`. Establish `: Algebra.IsIntegral A B` using `⟨hb⟩`. Establish `: (M.comap v.hom).IsPrime` using `Ideal.comap_isPrime v.hom M`. Establish `hA' : ((M.comap v.hom).comap (algebraMap A B)).IsMaximal`. Express the relevant statement in the definitionally equal form `((M.comap v.hom).comap b.hom).IsMaximal`.

Rewrite using `[hA]`. Conclude with `IsLocalRing.maximalIdeal.isMaximal A`. Conclude with `Ideal.isMaximal_of_isIntegral_of_isMaximal_comap _ hA'`. Conclude with `⟨hXe.symm.le, (IsLocalRing.eq_maximalIdeal hB).symm.le⟩`.
-/
theorem maxOver {A X B Z : CommRingCat.{0}} (x : A ⟶ X) (b : A ⟶ B) (u : X ⟶ Z) (v : B ⟶ Z) (hp : IsPushout x b u v)
    [IsLocalRing A] [IsLocalRing X] [IsLocalRing B] (hx : IsLocalHom x.hom) (hb : b.hom.IsIntegral)
    (M : Ideal Z) (hM : M.IsMaximal) :
    maximalIdeal X ≤ M.comap u.hom ∧ maximalIdeal B ≤ M.comap v.hom := by
  have hu : u.hom.IsIntegral := LateralTheory.E.SHTensorPf.intPush hp hb
  have hX : (M.comap u.hom).IsMaximal := by
    let _ := u.hom.toAlgebra
    have : Algebra.IsIntegral X Z := ⟨hu⟩
    exact Ideal.isMaximal_comap_of_isIntegral_of_isMaximal M
  have hXe : M.comap u.hom = maximalIdeal X := IsLocalRing.eq_maximalIdeal hX
  have hw : u.hom.comp x.hom = v.hom.comp b.hom := by
    have := congrArg CommRingCat.Hom.hom hp.w; simpa using this
  have hA : ((M.comap v.hom).comap b.hom) = maximalIdeal A := by
    rw [Ideal.comap_comap, ← hw, ← Ideal.comap_comap, hXe]
    ext a
    simp only [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    exact not_congr (isUnit_map_iff x.hom a)
  have hB : (M.comap v.hom).IsMaximal := by
    let _ := b.hom.toAlgebra
    have : Algebra.IsIntegral A B := ⟨hb⟩
    have : (M.comap v.hom).IsPrime := Ideal.comap_isPrime v.hom M
    have hA' : ((M.comap v.hom).comap (algebraMap A B)).IsMaximal := by
      change ((M.comap v.hom).comap b.hom).IsMaximal
      rw [hA]; exact IsLocalRing.maximalIdeal.isMaximal A
    exact Ideal.isMaximal_of_isIntegral_of_isMaximal_comap _ hA'
  exact ⟨hXe.symm.le, (IsLocalRing.eq_maximalIdeal hB).symm.le⟩

open IsLocalRing in
/- English proof (translation)
Establish `hm : ((maximalIdeal B).comap b).IsMaximal`. Set `_` to `b.toAlgebra`. Establish `: Algebra.IsIntegral A B` using `⟨hb⟩`. Conclude with `Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (maximalIdeal B)`. Establish `he` using `IsLocalRing.eq_maximalIdeal hm`.

Use `⟨fun a ha => ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hna`. Establish `: a ∈ (maximalIdeal B).comap b` using `by rw [he]; exact hna`. Conclude with `(IsLocalRing.mem_maximalIdeal _).mp this ha`.
-/
theorem locHom_of_int {A B : Type} [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B] (b : A →+* B)
    (hb : b.IsIntegral) : IsLocalHom b := by
  have hm : ((maximalIdeal B).comap b).IsMaximal := by
    let _ := b.toAlgebra
    have : Algebra.IsIntegral A B := ⟨hb⟩
    exact Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (maximalIdeal B)
  have he := IsLocalRing.eq_maximalIdeal hm
  refine ⟨fun a ha => ?_⟩
  by_contra hna
  have : a ∈ (maximalIdeal B).comap b := by rw [he]; exact hna
  exact (IsLocalRing.mem_maximalIdeal _).mp this ha

open IsLocalRing in
/- English proof (translation)
Introduce `y`. Take `⟨y0, rfl⟩` from `IsLocalRing.residue_surjective y`. Take `⟨p, hpm, hp⟩` from `hb y0`. Establish `hc : (ResidueField.map b).comp (residue A) = (residue B).comp b`. Use extensionality with `a`.

Simplify using `[ResidueField.map_residue]`. Use `⟨p.map (residue A), hpm.map _, ?_⟩` and prove the remaining obligations. Rewrite using `[Polynomial.eval₂_map, hc, ← Polynomial.hom_eval₂, hp, map_zero]`.
-/
theorem resInt {A B : Type} [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B] (b : A →+* B)
    (hb : b.IsIntegral) [IsLocalHom b] : (ResidueField.map b).IsIntegral := by
  intro y
  obtain ⟨y0, rfl⟩ := IsLocalRing.residue_surjective y
  obtain ⟨p, hpm, hp⟩ := hb y0
  have hc : (ResidueField.map b).comp (residue A) = (residue B).comp b := by
    ext a; simp [ResidueField.map_residue]
  refine ⟨p.map (residue A), hpm.map _, ?_⟩
  rw [Polynomial.eval₂_map, hc, ← Polynomial.hom_eval₂, hp, map_zero]

open IsLocalRing in
/- English proof (translation)
Establish `: IsLocalHom b.hom` using `locHom_of_int b.hom hb`. Set `K` to `AlgebraicClosure (ResidueField X)`. Set `e : ResidueField A →+* K` to `(algebraMap (ResidueField X) K).comp (ResidueField.map x.hom)`. Set `_ : Algebra (ResidueField A) K` to `e.toAlgebra`. Set `_ : Algebra (ResidueField A) (ResidueField B)` to `(ResidueField.map b.hom).toAlgebra`.

Establish `: Algebra.IsIntegral (ResidueField A) (ResidueField B)` using `⟨resInt b.hom hb⟩`. Establish `: Algebra.IsAlgebraic (ResidueField A) (ResidueField B)` using `inferInstance`. Set `l : ResidueField B →ₐ[ResidueField A] K` to `IsAlgClosed.lift`. Set `f : X →+* K` to `(algebraMap (ResidueField X) K).comp (residue X)`. Set `g : B →+* K` to `l.toRingHom.comp (residue B)`.

Establish `hw : x ≫ CommRingCat.ofHom f = b ≫ CommRingCat.ofHom g`. Use extensionality with `a`. Simplify using `only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply, f, g]`. Rewrite using `[← ResidueField.map_residue x.hom, ← ResidueField.map_residue b.hom]`. Use `l.commutes (residue A a)` as an intermediate fact.

Simplify using `only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe]`. Rewrite using `[show (ResidueField.map b.hom) (residue A a) = algebraMap (ResidueField A) (ResidueField B) (residue A a) from rfl, this]`. Both sides reduce to the same expression. Set `d : Z ⟶ CommRingCat.of K` to `hp.desc (CommRingCat.ofHom f) (CommRingCat.ofHom g) hw`. Conclude with `d.hom.domain_nontrivial`.
-/
theorem nontriv {A X B Z : CommRingCat.{0}} (x : A ⟶ X) (b : A ⟶ B) (u : X ⟶ Z) (v : B ⟶ Z) (hp : IsPushout x b u v)
    [IsLocalRing A] [IsLocalRing X] [IsLocalRing B] (hx : IsLocalHom x.hom) (hb : b.hom.IsIntegral) : Nontrivial Z := by
  have : IsLocalHom b.hom := locHom_of_int b.hom hb
  let K := AlgebraicClosure (ResidueField X)
  let e : ResidueField A →+* K := (algebraMap (ResidueField X) K).comp (ResidueField.map x.hom)
  let _ : Algebra (ResidueField A) K := e.toAlgebra
  let _ : Algebra (ResidueField A) (ResidueField B) := (ResidueField.map b.hom).toAlgebra
  have : Algebra.IsIntegral (ResidueField A) (ResidueField B) := ⟨resInt b.hom hb⟩
  have : Algebra.IsAlgebraic (ResidueField A) (ResidueField B) := inferInstance
  let l : ResidueField B →ₐ[ResidueField A] K := IsAlgClosed.lift
  let f : X →+* K := (algebraMap (ResidueField X) K).comp (residue X)
  let g : B →+* K := l.toRingHom.comp (residue B)
  have hw : x ≫ CommRingCat.ofHom f = b ≫ CommRingCat.ofHom g := by
    ext a
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply, f, g]
    rw [← ResidueField.map_residue x.hom, ← ResidueField.map_residue b.hom]
    have := l.commutes (residue A a)
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
    rw [show (ResidueField.map b.hom) (residue A a) = algebraMap (ResidueField A) (ResidueField B) (residue A a) from rfl, this]
    rfl
  let d : Z ⟶ CommRingCat.of K := hp.desc (CommRingCat.ofHom f) (CommRingCat.ofHom g) hw
  exact d.hom.domain_nontrivial

/- English proof (translation)
Break down `hq with rfl | ⟨hpr, h0⟩` into its components or cases. Simplify using the standard rewrite rules. Break down `subsingleton_or_nontrivial R with hs | hs` into its components or cases. Conclude with `Subsingleton.elim _ _`. Establish `: Fact q.Prime` using `⟨hpr⟩`.

Establish `: CharP R q` using `(CharP.charP_iff_prime_eq_zero hpr).mpr h0`. Conclude with `add_pow_char_pow a b q n`.
-/
theorem frobAdd {R : Type} [CommRing R] (q n : ℕ) (hq : q = 1 ∨ (q.Prime ∧ (q : R) = 0)) (a b : R) :
    (a + b) ^ (q ^ n) = a ^ (q ^ n) + b ^ (q ^ n) := by
  rcases hq with rfl | ⟨hpr, h0⟩
  · simp
  · rcases subsingleton_or_nontrivial R with hs | hs
    · exact Subsingleton.elim _ _
    · have : Fact q.Prime := ⟨hpr⟩
      have : CharP R q := (CharP.charP_iff_prime_eq_zero hpr).mpr h0
      exact add_pow_char_pow a b q n

/- English proof (translation)
Use `set T := Subring.closure (Set.range u.hom ∪ Set.range v.hom)`. Set `u' : X ⟶ CommRingCat.of T` to `CommRingCat.ofHom (u.hom.codRestrict T (fun y => Subring.subset_closure (Or.inl ⟨y, rfl⟩)))`. Set `v' : B ⟶ CommRingCat.of T` to `CommRingCat.ofHom (v.hom.codRestrict T (fun y => Subring.subset_closure (Or.inr ⟨y, rfl⟩)))`. Set `ι : CommRingCat.of T ⟶ Z` to `CommRingCat.ofHom T.subtype`. Establish `hw : x ≫ u' = b ≫ v'`.

Use extensionality with `a`. Use `congrArg (fun f => f.hom a) hp.w` as an intermediate fact. Simplify `this` using `[u', v']`. Set `s` to `hp.desc u' v' hw`. Establish `hs : s ≫ ι = 𝟙 Z`.

Apply `hp.hom_ext` to reduce the goal to its premises. Rewrite using `[← Category.assoc, hp.inl_desc]`. Use extensionality with `y`. Both sides reduce to the same expression. Rewrite using `[← Category.assoc, hp.inr_desc]`.

Use extensionality with `y`. Both sides reduce to the same expression. Establish `: z = ι.hom (s.hom z)`. Use `congrArg (fun f => f.hom z) hs` as an intermediate fact. Simplify using `using this.symm`.

Rewrite using `[this]`. Conclude with `(s.hom z).2`.
-/
theorem gen {A X B Z : CommRingCat.{0}} {x : A ⟶ X} {b : A ⟶ B} {u : X ⟶ Z} {v : B ⟶ Z} (hp : IsPushout x b u v)
    (z : Z) : z ∈ Subring.closure (Set.range u.hom ∪ Set.range v.hom) := by
  set T := Subring.closure (Set.range u.hom ∪ Set.range v.hom)
  let u' : X ⟶ CommRingCat.of T := CommRingCat.ofHom (u.hom.codRestrict T
    (fun y => Subring.subset_closure (Or.inl ⟨y, rfl⟩)))
  let v' : B ⟶ CommRingCat.of T := CommRingCat.ofHom (v.hom.codRestrict T
    (fun y => Subring.subset_closure (Or.inr ⟨y, rfl⟩)))
  let ι : CommRingCat.of T ⟶ Z := CommRingCat.ofHom T.subtype
  have hw : x ≫ u' = b ≫ v' := by
    ext a
    have := congrArg (fun f => f.hom a) hp.w
    simpa [u', v'] using this
  let s := hp.desc u' v' hw
  have hs : s ≫ ι = 𝟙 Z := by
    apply hp.hom_ext
    · rw [← Category.assoc, hp.inl_desc]; ext y; rfl
    · rw [← Category.assoc, hp.inr_desc]; ext y; rfl
  have : z = ι.hom (s.hom z) := by
    have := congrArg (fun f => f.hom z) hs; simpa using this.symm
  rw [this]; exact (s.hom z).2

open IsLocalRing in
/- English proof (translation)
Establish `: IsLocalHom b.hom` using `locHom_of_int b.hom hb`. Use `set J := Ideal.map u.hom (maximalIdeal X) ⊔ Ideal.map v.hom (maximalIdeal B) with hJ`. Establish `hw : u.hom.comp x.hom = v.hom.comp b.hom`. Use `congrArg CommRingCat.Hom.hom hp.w` as an intermediate fact. Simplify using `using this`.

Establish `hwa : ∀ a, u.hom (x.hom a) = v.hom (b.hom a)` using `fun a => by`. Use `congrArg (fun f => f a) hw` as an intermediate fact. Simplify using `using this`. Establish `huJ : ∀ y ∈ maximalIdeal X, u.hom y ∈ J` using `fun y hy => Ideal.mem_sup_left (Ideal.mem_map_of_mem _ hy)`. Establish `hvJ : ∀ y ∈ maximalIdeal B, v.hom y ∈ J` using `fun y hy => Ideal.mem_sup_right (Ideal.mem_map_of_mem _ hy)`.

Use `set q := ringExpChar (ResidueField A) with hqdef`. Establish `hexp : ExpChar (ResidueField A) q` using `ringExpChar.expChar _`. Establish `key : ∀ r : ℕ, ExpChar (ResidueField A) r → r = 1 ∨ (r.Prime ∧ ((r : ℕ) : Z ⧸ J) = 0)`. Introduce `q hexp`. Break down `hexp with _ | ⟨hpr⟩` into its components or cases.

Use `left`. Both sides reduce to the same expression. Use `right`. Use `⟨hpr, ?_⟩` and prove the remaining obligations. Establish `h1 : ((q : A)) ∈ maximalIdeal A`.

Rewrite using `[← IsLocalRing.residue_eq_zero_iff, map_natCast]`. Conclude with `CharP.cast_eq_zero _ q`. Establish `h2 : x.hom (q : A) ∈ maximalIdeal X` using `map_nonunit x.hom _ h1`. Establish `h3` using `huJ _ h2`. Rewrite `h3` using `[map_natCast, map_natCast]`.

Rewrite using `[← map_natCast (Ideal.Quotient.mk J)]`. Conclude with `Ideal.Quotient.eq_zero_iff_mem.mpr h3`. Establish `hq` using `key q hexp`. Establish `hq1 : 0 < q` using `by rcases hq with h | ⟨h, _⟩; · omega`. Conclude with `h.pos`.

Set `mk` to `Ideal.Quotient.mk J`. Set `P : Z → Prop` to `fun z => ∃ n : ℕ, ∃ y : X, mk (z ^ (q ^ n)) = mk (u.hom y)`. Establish `lift : ∀ z n k y, mk (z ^ (q ^ n)) = mk (u.hom y) → mk (z ^ (q ^ (n + k))) = mk (u.hom (y ^ (q ^ k)))`. Introduce `z n k y h`. Rewrite using `[pow_add, pow_mul, map_pow, h, ← map_pow, ← map_pow]`.

Establish `hadd : ∀ z w, P z → P w → P (z + w)`. Introduce and unpack `z w ⟨n, y, hy⟩ ⟨m, y', hy'⟩`. Use `⟨n + m, y ^ (q ^ m) + y' ^ (q ^ n), ?_⟩` and prove the remaining obligations. Rewrite using `[map_pow, map_add, frobAdd q _ hq, ← map_pow, ← map_pow, lift z n m y hy, add_comm n m, lift w m n y' hy', map_add, map_add]`. Establish `hmul : ∀ z w, P z → P w → P (z * w)`.

Introduce and unpack `z w ⟨n, y, hy⟩ ⟨m, y', hy'⟩`. Use `⟨n + m, y ^ (q ^ m) * y' ^ (q ^ n), ?_⟩` and prove the remaining obligations. Rewrite using `[mul_pow, map_mul, lift z n m y hy, add_comm n m, lift w m n y' hy', map_mul, map_mul]`. Establish `hu : ∀ y, P (u.hom y)` using `fun y => ⟨0, y, by simp⟩`. Establish `hv : ∀ y, P (v.hom y)`.

Introduce `y`. Set `_ : Algebra (ResidueField A) (ResidueField B)` to `(ResidueField.map b.hom).toAlgebra`. Establish `: Algebra.IsIntegral (ResidueField A) (ResidueField B)` using `⟨resInt b.hom hb⟩`. Establish `: Algebra.IsAlgebraic (ResidueField A) (ResidueField B)` using `inferInstance`. Establish `: IsPurelyInseparable (ResidueField A) (ResidueField B)` using `Algebra.IsAlgebraic.isPurelyInseparable_of_isSepClosed`.

Take `⟨n, c, hc⟩` from `IsPurelyInseparable.pow_mem (ResidueField A) q (residue B y)`. Take `⟨a, rfl⟩` from `IsLocalRing.residue_surjective c`. Use `⟨n, x.hom a, ?_⟩` and prove the remaining obligations. Establish `h1 : y ^ (q ^ n) - b.hom a ∈ maximalIdeal B`. Rewrite using `[← IsLocalRing.residue_eq_zero_iff, map_sub, map_pow, ← hc]`.

Express the relevant statement in the definitionally equal form `ResidueField.map b.hom (residue A a) - _ = 0`. Rewrite using `[ResidueField.map_residue, sub_self]`. Establish `h2` using `hvJ _ h1`. Rewrite `h2` using `[map_sub, map_pow, ← hwa]`. Conclude with `Ideal.Quotient.eq.mpr h2`.

Establish `hz : P z`. Establish `hg` using `gen hp z`. Proceed by induction on `hg using Subring.closure_induction with`. Consider the case `mem w hw' => rcases hw' with ⟨y, rfl⟩ | ⟨y, rfl⟩`. Use `exacts [hu y, hv y]`.

Consider the case `zero => exact ⟨0, 0, by simp⟩`. Consider the case `one => exact ⟨0, 1, by simp⟩`. Consider the case `add _ _ _ _ h1 h2 => exact hadd _ _ h1 h2`. Consider the case `neg w _ h`. Establish `: -w = u.hom (-1) * w` using `by simp`.

Rewrite using `[this]`. Conclude with `hmul _ _ (hu _) h`. Consider the case `mul _ _ _ _ h1 h2 => exact hmul _ _ h1 h2`. Take `⟨n, y, hy⟩` from `hz`. Conclude with `⟨q ^ n, pow_pos hq1 n, y, Ideal.Quotient.eq.mp hy⟩`.
-/
theorem frob {A X B Z : CommRingCat.{0}} (x : A ⟶ X) (b : A ⟶ B) (u : X ⟶ Z) (v : B ⟶ Z) (hp : IsPushout x b u v)
    [IsLocalRing A] [IsLocalRing X] [IsLocalRing B] [IsSepClosed (ResidueField A)]
    (hx : IsLocalHom x.hom) (hb : b.hom.IsIntegral) (z : Z) : ∃ N : ℕ, 0 < N ∧ ∃ y : X,
      z ^ N - u.hom y ∈ Ideal.map u.hom (maximalIdeal X) ⊔ Ideal.map v.hom (maximalIdeal B) := by
  have : IsLocalHom b.hom := locHom_of_int b.hom hb
  set J := Ideal.map u.hom (maximalIdeal X) ⊔ Ideal.map v.hom (maximalIdeal B) with hJ
  have hw : u.hom.comp x.hom = v.hom.comp b.hom := by
    have := congrArg CommRingCat.Hom.hom hp.w; simpa using this
  have hwa : ∀ a, u.hom (x.hom a) = v.hom (b.hom a) := fun a => by
    have := congrArg (fun f => f a) hw; simpa using this
  have huJ : ∀ y ∈ maximalIdeal X, u.hom y ∈ J := fun y hy =>
    Ideal.mem_sup_left (Ideal.mem_map_of_mem _ hy)
  have hvJ : ∀ y ∈ maximalIdeal B, v.hom y ∈ J := fun y hy =>
    Ideal.mem_sup_right (Ideal.mem_map_of_mem _ hy)
  set q := ringExpChar (ResidueField A) with hqdef
  have hexp : ExpChar (ResidueField A) q := ringExpChar.expChar _
  have key : ∀ r : ℕ, ExpChar (ResidueField A) r → r = 1 ∨ (r.Prime ∧ ((r : ℕ) : Z ⧸ J) = 0) := by
    intro q hexp
    rcases hexp with _ | ⟨hpr⟩
    · left; rfl
    · right; refine ⟨hpr, ?_⟩
      have h1 : ((q : A)) ∈ maximalIdeal A := by
        rw [← IsLocalRing.residue_eq_zero_iff, map_natCast]; exact CharP.cast_eq_zero _ q
      have h2 : x.hom (q : A) ∈ maximalIdeal X := map_nonunit x.hom _ h1
      have h3 := huJ _ h2
      rw [map_natCast, map_natCast] at h3
      rw [← map_natCast (Ideal.Quotient.mk J)]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr h3
  have hq := key q hexp
  have hq1 : 0 < q := by rcases hq with h | ⟨h, _⟩; · omega
                         · exact h.pos
  let mk := Ideal.Quotient.mk J
  let P : Z → Prop := fun z => ∃ n : ℕ, ∃ y : X, mk (z ^ (q ^ n)) = mk (u.hom y)
  have lift : ∀ z n k y, mk (z ^ (q ^ n)) = mk (u.hom y) → mk (z ^ (q ^ (n + k))) = mk (u.hom (y ^ (q ^ k))) := by
    intro z n k y h
    rw [pow_add, pow_mul, map_pow, h, ← map_pow, ← map_pow]
  have hadd : ∀ z w, P z → P w → P (z + w) := by
    rintro z w ⟨n, y, hy⟩ ⟨m, y', hy'⟩
    refine ⟨n + m, y ^ (q ^ m) + y' ^ (q ^ n), ?_⟩
    rw [map_pow, map_add, frobAdd q _ hq, ← map_pow, ← map_pow, lift z n m y hy, add_comm n m,
      lift w m n y' hy', map_add, map_add]
  have hmul : ∀ z w, P z → P w → P (z * w) := by
    rintro z w ⟨n, y, hy⟩ ⟨m, y', hy'⟩
    refine ⟨n + m, y ^ (q ^ m) * y' ^ (q ^ n), ?_⟩
    rw [mul_pow, map_mul, lift z n m y hy, add_comm n m, lift w m n y' hy', map_mul, map_mul]
  have hu : ∀ y, P (u.hom y) := fun y => ⟨0, y, by simp⟩
  have hv : ∀ y, P (v.hom y) := by
    intro y
    let _ : Algebra (ResidueField A) (ResidueField B) := (ResidueField.map b.hom).toAlgebra
    have : Algebra.IsIntegral (ResidueField A) (ResidueField B) := ⟨resInt b.hom hb⟩
    have : Algebra.IsAlgebraic (ResidueField A) (ResidueField B) := inferInstance
    have : IsPurelyInseparable (ResidueField A) (ResidueField B) :=
      Algebra.IsAlgebraic.isPurelyInseparable_of_isSepClosed
    obtain ⟨n, c, hc⟩ := IsPurelyInseparable.pow_mem (ResidueField A) q (residue B y)
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective c
    refine ⟨n, x.hom a, ?_⟩
    have h1 : y ^ (q ^ n) - b.hom a ∈ maximalIdeal B := by
      rw [← IsLocalRing.residue_eq_zero_iff, map_sub, map_pow, ← hc]
      change ResidueField.map b.hom (residue A a) - _ = 0
      rw [ResidueField.map_residue, sub_self]
    have h2 := hvJ _ h1
    rw [map_sub, map_pow, ← hwa] at h2
    exact Ideal.Quotient.eq.mpr h2
  have hz : P z := by
    have hg := gen hp z
    induction hg using Subring.closure_induction with
    | mem w hw' => rcases hw' with ⟨y, rfl⟩ | ⟨y, rfl⟩; exacts [hu y, hv y]
    | zero => exact ⟨0, 0, by simp⟩
    | one => exact ⟨0, 1, by simp⟩
    | add _ _ _ _ h1 h2 => exact hadd _ _ h1 h2
    | neg w _ h =>
      have : -w = u.hom (-1) * w := by simp
      rw [this]; exact hmul _ _ (hu _) h
    | mul _ _ _ _ h1 h2 => exact hmul _ _ h1 h2
  obtain ⟨n, y, hy⟩ := hz
  exact ⟨q ^ n, pow_pos hq1 n, y, Ideal.Quotient.eq.mp hy⟩

/- English proof (translation)
Introduce `A X B Z x b u v hp hA hX hx hb hB`. Take `⟨hAh, hAs⟩` from `hA`. Take `⟨hXh, _⟩` from `hX`. Use `nontriv x b u v hp hx hb` as an intermediate fact. Conclude with `isLocalRing_of_maximal_over_and_power_in_range Z X B u.hom v.hom (fun M hM => maxOver x b u v hp hx hb M hM) (frob x b u v hp hx hb)`.
-/
theorem LocTensor_of : LateralTheory.E.SHTensorPf.LocTensor := by
  intro A X B Z x b u v hp hA hX hx hb hB
  obtain ⟨hAh, hAs⟩ := hA
  obtain ⟨hXh, _⟩ := hX
  have := nontriv x b u v hp hx hb
  exact isLocalRing_of_maximal_over_and_power_in_range Z X B u.hom v.hom (fun M hM => maxOver x b u v hp hx hb M hM) (frob x b u v hp hx hb)

end LateralTheory.E.LocTensorPf
