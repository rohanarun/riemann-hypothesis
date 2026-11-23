module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.Counts
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GeneratorCountTuples.LemmaK
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.ClsOnto
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0003
public import Formalism.GaloisCohomology.LocalTateDualityK
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.HcDefs
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.HostNumber
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.Bundle0004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.Bundle0005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.Bundle0007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.Bundle0008
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.Bundle0001

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.ChrInvNeg
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Odd UpperTheory.V.ML UpperTheory.V.X

private theorem cls_onto {Ω : Type} [Field Ω] [inst : Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (N : ℕ) [NeZero N] :
    Function.Surjective (Chr.cls ℚ Ω N) := by
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  obtain rfl : inst = DivisionRing.toRatAlgebra := Subsingleton.elim _ _
  exact (Chr.clsOnto Ω N).1

private theorem red_chi {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime]
    {O k : Type} [CommRing O] [Algebra ℤ_[l] O] [Field k] [CharP k l] (red : O →+* k) (g : G ℚ Ω)
    (h : ∀ t : Ω, t ^ l = 1 → g t = t) : red (chiO ℚ Ω l O g : O) = 1 := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  haveI : NeZero l := ⟨(Fact.out : l.Prime).ne_zero⟩
  haveI hE : ∀ i, HasEnoughRootsOfUnity Ω (l ^ i) := fun i => inferInstance
  have hpow : ∀ t : Ω, t ^ l ^ 1 = 1 → t ^ (1 : ZMod (l ^ 1)).val = t := by
    intro t ht
    rw [ZMod.val_one_eq_one_mod, ← pow_eq_pow_mod _ ht, pow_one]
  have h1 : (cyclotomicCharacter Ω l g.toRingEquiv).val.toZModPow 1 = 1 := by
    rw [cyclotomicCharacter.toZModPow]
    refine (modularCyclotomicCharacter.unique Ω _ _ fun t ht => ?_).symm
    have ht' : (t : Ω) ^ l ^ 1 = 1 := by
      rw [← Units.val_pow_eq_pow_val, (mem_rootsOfUnity _ _).1 ht, Units.val_one]
    rw [hpow _ ht']
    exact h _ (by rwa [pow_one] at ht')
  rw [← sub_eq_zero, ← map_one (PadicInt.toZModPow (p := l) 1), ← map_sub, ← RingHom.mem_ker, PadicInt.ker_toZModPow,
    pow_one, Ideal.mem_span_singleton] at h1
  obtain ⟨y, hy⟩ := h1
  have e : (chiO ℚ Ω l O g : O) = algebraMap ℤ_[l] O (cyclotomicCharacter Ω l g.toRingEquiv).val := rfl
  rw [e, sub_eq_iff_eq_add.1 hy]
  simp

private theorem prodX_unit {R : Type} [CommRing R] {f n : ℕ} (φ : DirichletCharacter R f) (ξ : DirichletCharacter R (2 ^ n))
    (u : (ZMod (f * 2 ^ n))ˣ) :
    prodX φ ξ (u : ZMod (f * 2 ^ n)) = φ (ZMod.cast (u : ZMod (f * 2 ^ n))) * ξ (ZMod.cast (u : ZMod (f * 2 ^ n))) := by
  rw [prodX, MulChar.mul_apply, DirichletCharacter.changeLevel_eq_cast_of_dvd, DirichletCharacter.changeLevel_eq_cast_of_dvd]

private theorem prodX_map {R S : Type} [CommRing R] [CommRing S] (j : R →+* S) {f n : ℕ} (φ : DirichletCharacter R f)
    (ξ : DirichletCharacter R (2 ^ n)) : (prodX φ ξ).ringHomComp j = prodX (φ.ringHomComp j) (ξ.ringHomComp j) := by
  ext u
  rw [MulChar.ringHomComp_apply, prodX_unit, prodX_unit, map_mul, MulChar.ringHomComp_apply, MulChar.ringHomComp_apply]

private theorem prodX_inv {R : Type} [CommRing R] {f n : ℕ} (φ : DirichletCharacter R f)
    (ξ : DirichletCharacter R (2 ^ n)) : (prodX φ ξ)⁻¹ = prodX φ⁻¹ ξ⁻¹ := by
  rw [prodX, prodX, mul_inv, map_inv, map_inv]

private theorem chr_inv_neg {R : Type} [CommRing R] {N : ℕ} (χ : DirichletCharacter R N) : χ⁻¹ (-1) = χ (-1) := by
  rw [MulChar.inv_apply]
  congr 1
  have : ((-1 : (ZMod N)ˣ) : ZMod N) = -1 := by simp
  rw [← this, Ring.inverse_unit]
  simp

private theorem xd_inv {l d : ℕ} {R : Type} [CommRing R] {f n : ℕ} {φ : DirichletCharacter R f}
    {ξ : DirichletCharacter R (2 ^ n)} (h : XData l d φ ξ) : XData l d φ⁻¹ ξ⁻¹ := by
  refine ⟨h.d_pos, h.four, h.f_odd, h.prim.inv, ?_, h.prim2.inv, h.big, ?_⟩
  · simpa only [orderOf_inv] using h.ord
  · simpa only [chr_inv_neg] using h.odd

private theorem xd_map {l d : ℕ} {R S : Type} [CommRing R] [CommRing S] (j : R →+* S) (hj : Function.Injective j) {f n : ℕ}
    {φ : DirichletCharacter R f} {ξ : DirichletCharacter R (2 ^ n)} (h : XData l d φ ξ) :
    XData l d (φ.ringHomComp j) (ξ.ringHomComp j) := by
  haveI : NeZero f := ⟨h.f_odd.pos.ne'⟩
  refine ⟨h.d_pos, h.four, h.f_odd, ?_, ?_, ?_, h.big, ?_⟩
  · rw [DirichletCharacter.isPrimitive_def, (Bern.b_condmap j hj φ).1]; exact h.prim
  · rw [orderOf_dvd_iff_pow_eq_one, MulChar.ringHomComp_pow, orderOf_dvd_iff_pow_eq_one.1 h.ord, MulChar.ringHomComp_one]
  · rw [DirichletCharacter.isPrimitive_def, (Bern.b_condmap j hj ξ).1]; exact h.prim2
  · rw [MulChar.ringHomComp_apply, MulChar.ringHomComp_apply, ← map_mul, h.odd, map_neg, map_one]

private theorem xd_pos {l d : ℕ} (hl : l.Prime) (hd : 0 < d) : 0 < l ^ d - 1 :=
  Nat.sub_pos_of_lt (Nat.one_lt_pow hd.ne' hl.one_lt)

private theorem xd_ne_two {l d : ℕ} (hd : 0 < d) (h : 4 ∣ l ^ d - 1) : l ≠ 2 := by
  rintro rfl
  obtain ⟨e, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hd.ne'
  have : 0 < 2 ^ e := by positivity
  rw [pow_succ] at h
  omega

private theorem xi_pow {R : Type} [CommRing R] {n : ℕ} (ξ : DirichletCharacter R (2 ^ n)) (u : (ZMod (2 ^ n))ˣ) :
    ξ (u : ZMod (2 ^ n)) ^ 2 ^ n = 1 := by
  have h1 : Nat.totient (2 ^ n) ∣ 2 ^ n := by
    rcases n with _ | m
    · simp
    · rw [Nat.totient_prime_pow_succ Nat.prime_two]; simp [pow_succ]
  obtain ⟨e, he⟩ := h1
  rw [← map_pow, ← Units.val_pow_eq_pow_val]
  conv_lhs => enter [2, 1, 2]; rw [he]
  rw [pow_mul, ZMod.pow_totient, one_pow, Units.val_one, map_one]

private theorem xd_ord {l d : ℕ} (hl : l.Prime) {R : Type} [CommRing R] {f n : ℕ}
    {φ : DirichletCharacter R f} {ξ : DirichletCharacter R (2 ^ n)} (h : XData l d φ ξ) : ¬ l ∣ orderOf (prodX φ ξ) := by
  have h1 : ξ ^ 2 ^ n = 1 := by
    ext u
    rw [MulChar.pow_apply_coe, xi_pow, MulChar.one_apply_coe]
  have h2 : prodX φ ξ ^ ((l ^ d - 1) * 2 ^ n) = 1 := by
    rw [prodX, mul_pow, ← map_pow, ← map_pow, pow_mul, orderOf_dvd_iff_pow_eq_one.1 h.ord, pow_mul', h1]
    simp
  intro hd
  rcases (Nat.Prime.dvd_mul hl).1 (hd.trans (orderOf_dvd_of_pow_eq_one h2)) with h3 | h3
  · have h4 : l ∣ l ^ d := dvd_pow_self l h.d_pos.ne'
    have h5 := (Nat.dvd_sub_iff_right (Nat.one_le_pow d l hl.pos) h4).1 h3
    exact hl.one_lt.ne' (Nat.dvd_one.1 h5)
  · exact xd_ne_two h.d_pos h.four ((Nat.prime_dvd_prime_iff_eq hl Nat.prime_two).1 (hl.dvd_of_dvd_pow h3))

private theorem neg_one_of {R : Type} [CommRing R] [IsDomain R] (x : R) (hx : x ≠ 1) :
    ∀ m : ℕ, x ^ 2 ^ m = 1 → ∃ j : ℕ, x ^ j = -1 := by
  intro m
  induction m with
  | zero => intro h; exact absurd (by simpa using h) hx
  | succ m ih =>
    intro h
    rw [pow_succ, pow_mul, pow_two, mul_self_eq_one_iff] at h
    exact h.elim ih fun h => ⟨_, h⟩

private theorem xd_neg {l d : ℕ} (hl : l.Prime) {R : Type} [CommRing R] [IsDomain R] {f n : ℕ}
    {φ : DirichletCharacter R f} {ξ : DirichletCharacter R (2 ^ n)} (h : XData l d φ ξ) :
    ∃ b : (ZMod (2 ^ n))ˣ, ξ (b : ZMod (2 ^ n)) = -1 := by
  have h0 : 1 ≤ (l ^ d - 1).factorization 2 :=
    (Nat.prime_two.dvd_iff_one_le_factorization (xd_pos hl h.d_pos).ne').1 (dvd_trans (by norm_num) h.four)
  have h1 : 4 ≤ 2 ^ n := by
    refine le_trans ?_ h.big
    calc 4 = 1 * 4 ^ 1 := by norm_num
      _ ≤ _ := Nat.mul_le_mul h.f_odd.pos (Nat.pow_le_pow_right (by norm_num) h0)
  have h2 : ξ ≠ 1 := by
    rintro rfl
    have := h.prim2
    rw [DirichletCharacter.isPrimitive_def, DirichletCharacter.conductor_one] at this
    omega
  obtain ⟨u, hu⟩ := MulChar.ne_one_iff.1 h2
  obtain ⟨j, hj⟩ := neg_one_of _ hu n (xi_pow ξ u)
  exact ⟨u ^ j, by rw [Units.val_pow_eq_pow_val, map_pow, hj]⟩

private theorem xd_gal {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] {l d : ℕ} (hl : l.Prime) {R : Type} [CommRing R]
    [IsDomain R] {f n : ℕ} [NeZero (f * 2 ^ n)] {φ : DirichletCharacter R f} {ξ : DirichletCharacter R (2 ^ n)}
    (h : XData l d φ ξ) :
    ∃ g : G ℚ Ω, (∀ t : Ω, t ^ l = 1 → g t = t) ∧ (Chr.dirG ℚ Ω (prodX φ ξ) g : R) = -1 := by
  obtain ⟨b, hb⟩ := xd_neg hl h
  have hodd : Odd (l * f) := (hl.odd_of_ne_two (xd_ne_two h.d_pos h.four)).mul h.f_odd
  have hco : (l * f).Coprime (2 ^ n) := (Nat.coprime_two_right.2 hodd).pow_right n
  obtain ⟨a, ha1, ha2⟩ := Nat.chineseRemainder hco 1 (b : ZMod (2 ^ n)).val
  have hc : a.Coprime (l * f * 2 ^ n) := by
    refine Nat.Coprime.mul_right ?_ ?_
    · rw [Nat.Coprime, ha1.gcd_eq]; simp
    · rw [Nat.Coprime, ha2.gcd_eq]; exact ZMod.val_coe_unit_coprime b
  haveI : NeZero (l * f * 2 ^ n) := ⟨mul_ne_zero hodd.pos.ne' (by positivity)⟩
  obtain ⟨g, hg⟩ := cls_onto (Ω := Ω) (l * f * 2 ^ n) (ZMod.unitOfCoprime a hc)
  refine ⟨g, fun t ht => ?_, ?_⟩
  · have hM : t ^ (l * f * 2 ^ n) = 1 := by rw [mul_assoc, pow_mul, ht, one_pow]
    rw [Chr.cls_spec _ g t hM, hg, ZMod.coe_unitOfCoprime, ZMod.val_natCast, ← pow_eq_pow_mod _ hM,
      pow_eq_pow_mod _ ht, ha1.of_mul_right f, ← pow_eq_pow_mod _ ht, pow_one]
  · have hd : f * 2 ^ n ∣ l * f * 2 ^ n := by rw [mul_assoc]; exact dvd_mul_left _ _
    have e1 : ((Chr.cls ℚ Ω (f * 2 ^ n) g : (ZMod (f * 2 ^ n))ˣ) : ZMod (f * 2 ^ n)) = a := by
      rw [← (Chr.clsFacts ℚ Ω (l * f * 2 ^ n)).2.1 _ hd, MonoidHom.comp_apply, hg, ZMod.unitsMap_val,
        ZMod.coe_unitOfCoprime, ZMod.cast_natCast hd]
    rw [Chr.dirG, MonoidHom.comp_apply, MulChar.coe_toUnitHom, prodX_unit, e1, ZMod.cast_natCast (dvd_mul_right _ _),
      ZMod.cast_natCast (dvd_mul_left _ _), (ZMod.natCast_eq_natCast_iff _ _ _).2 (ha1.of_mul_left l),
      (ZMod.natCast_eq_natCast_iff _ _ _).2 ha2, ZMod.natCast_zmod_val, hb]
    simp

private theorem chrInvNeg (hX : LemmaX) (h16 : UnramifiedCocycleIsCoboundaryOfBernoulliUnit) (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime]
    (c : HV.Coef l) (k : Type) [Field k] [CharP k l] (red : c.O →+* k) (d f n : ℕ) [NeZero (f * 2 ^ n)]
    (φ : DirichletCharacter c.O f) (ξ : DirichletCharacter c.O (2 ^ n)) (h : XData l d φ ξ) (z : G ℚ Ω → k)
    (hz : IsCoc (redChar Ω red (prodX φ ξ)) z) (hu : UnrEv l (redChar Ω red (prodX φ ξ)) z) :
    ∃ m : k, ∀ g, z g = (redChar Ω red (prodX φ ξ) g : k) * m - m := by
  have hl : l.Prime := Fact.out
  have h2 := xd_ne_two h.d_pos h.four
  obtain ⟨g, hg1, hg2⟩ := xd_gal (Ω := Ω) hl h
  have hne : (-1 : k) ≠ 1 := by
    intro e
    have : ((2 : ℕ) : k) = 0 := by rw [Nat.cast_ofNat, ← one_add_one_eq_two]; nth_rewrite 1 [← e]; simp
    exact h2 ((Nat.prime_dvd_prime_iff_eq hl Nat.prime_two).1 ((CharP.cast_eq_zero_iff k l 2).1 this))
  have hg3 : (redChar Ω red (prodX φ ξ) g : k) = -1 := by
    have : (redChar Ω red (prodX φ ξ) g : k) = red (Chr.dirG ℚ Ω (prodX φ ξ) g : c.O) := rfl
    rw [this, hg2, map_neg, map_one]
  refine h16 Ω l h2 c k red _ (prodX φ ξ) (fun e => hne ?_) (xd_ord hl h) ⟨g, ?_⟩ ?_ z hz hu
  · rw [← hg3, e, redChar, Chr.dirG]
    simp
  · rw [hg3, red_chi l red g hg1]; exact hne
  · rw [prodX_inv, prodX_map]
    exact hX l d f n _ _ (xd_map _ Subtype.val_injective (xd_inv h))

theorem UpperTheory.V.X.corX :
    LemmaX → UnramifiedCocycleIsCoboundaryOfBernoulliUnit → CorX := by
  intro hX h16 Ω _ _ _ l _ c k _ _ red d f n _ φ ξ h γ hγ z hz hu
  rcases hγ with rfl | rfl
  · exact chrInvNeg hX h16 Ω l c k red d f n φ ξ h z hz hu
  · have e : (redChar Ω red (prodX φ ξ))⁻¹ = redChar Ω red (prodX φ⁻¹ ξ⁻¹) := by
      rw [← prodX_inv, inv_eq_iff_mul_eq_one]
      ext g
      have : ∀ χ : DirichletCharacter c.O (f * 2 ^ n), (redChar Ω red χ g : k) = red (χ (Chr.cls ℚ Ω (f * 2 ^ n) g : (ZMod (f * 2 ^ n))ˣ)) :=
        fun χ => congrArg red (MulChar.coe_toUnitHom χ _)
      rw [MonoidHom.mul_apply, Units.val_mul, this, this, ← map_mul, ← MulChar.mul_apply, mul_inv_cancel, MulChar.one_apply_coe]
      simp
    rw [e] at hz hu ⊢
    exact chrInvNeg hX h16 Ω l c k red d f n _ _ (xd_inv h) z hz hu
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.HcDirData
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.X

private theorem sq_neg_one {O : Type} [CommRing O] {N : ℕ} (χ : DirichletCharacter O N) :
    χ ((-1 : ℤ) : ZMod N) ^ 2 = 1 := by
  have h : ((-1 : ℤ) : ZMod N) ^ 2 = 1 := by
    push_cast
    exact neg_one_sq
  first
    | rw [← map_pow, h, map_one]
    | rw [sq, ← χ.map_mul, ← sq, h, χ.map_one]

private theorem pow_app {O : Type} [CommRing O] {N : ℕ} (χ : DirichletCharacter O N) (k : ℕ) (a : ℤ)
    (ha : IsCoprime a (N : ℤ)) : (χ ^ k) (a : ZMod N) = χ a ^ k := by
  obtain ⟨u, v, huv⟩ := ha
  have h := congrArg (fun x : ℤ => (x : ZMod N)) huv
  simp only [Int.cast_add, Int.cast_mul, Int.cast_natCast, ZMod.natCast_self, mul_zero, add_zero,
    Int.cast_one] at h
  rw [← show ((⟨_, _, (mul_comm _ _).trans h, h⟩ : (ZMod N)ˣ) : ZMod N) = ((a : ℤ) : ZMod N) from rfl]
  exact MulChar.pow_apply_coe χ k _

theorem UpperTheory.V.X.dirData :
    ∀ (l : ℕ) [Fact l.Prime] (c : Coef l) (N : ℕ) [NeZero N] (e : ℕ) (ψ : DirichletCharacter c.O N) (o₁ : ℕ), UnitaryThreeInertia.HostData l e ψ o₁ → ∀ q : ℕ, UnitaryThreeInertia.XData l ψ q → ∀ ω : DirichletCharacter c.O l, ω ^ (l - 1) = 1 → ∃ (d f n : ℕ) (φ : DirichletCharacter c.O f) (ξ : DirichletCharacter c.O (2 ^ n)), XData l d φ ξ ∧ f * 2 ^ n ∣ l * N * N ∧ ∀ a : ℤ, IsCoprime a (l * N * N : ℕ) → prodX φ ξ a = (ω a ^ e * psi2 ψ a * th1 l ψ a) ^ 2 * ((ZMod.χ₄ a : ℤ) : c.O) := by
  intro l hl c N iN e ψ o₁ hD q hX ω hω
  have hl2 : l ≠ 2 := hD.l_odd
  have h4l : 4 ≤ c2 ψ := hD.four_le
  haveI : NeZero l := ⟨hl.out.ne_zero⟩
  obtain ⟨hq0, hq, hb⟩ := hX
  obtain ⟨-, -, hcod, hf0, hfour, hth, hl1⟩ := UpperTheory.V.X.th1Facts c.O N ψ l hl.out hl2
  obtain ⟨-, -, -, h2c, h2N, -⟩ := UpperTheory.V.HV.compCond c.O N ψ 2 Nat.prime_two
  obtain ⟨ξ, hξp, hξ⟩ :=
    UpperTheory.V.X.xiSq c.O two_ne_zero N (psi2 ψ) (c2 ψ) h4l h2c.symm
  obtain ⟨f, φ, hφp, hfd, hφo, hφ⟩ :=
    UpperTheory.V.X.primProd c.O l N ((ω ^ e) ^ 2) (th1 l ψ ^ 2)
  have hdiv : f * 2 ^ (c2 ψ - 1) ∣ l * N * N :=
    mul_dvd_mul (dvd_trans hfd (mul_dvd_mul_left l (DirichletCharacter.conductor_dvd_level _)))
      (dvd_trans (pow_dvd_pow 2 (Nat.sub_le _ 1)) h2N)
  have unitOf : ∀ (m : ℕ) (a : ℤ), IsCoprime a (m : ℤ) → IsUnit ((a : ZMod m)) := by
    rintro m a ⟨u, v, huv⟩
    have h := congrArg (fun x : ℤ => (x : ZMod m)) huv
    simp only [Int.cast_add, Int.cast_mul, Int.cast_natCast, ZMod.natCast_self, mul_zero, add_zero,
      Int.cast_one] at h
    exact ⟨⟨_, _, (mul_comm _ _).trans h, h⟩, rfl⟩
  refine ⟨f0 l ψ, f, c2 ψ - 1, φ, ξ, ?_, hdiv, ?_⟩
  · have hT : ((ω ^ e) ^ 2) ^ (l ^ f0 l ψ - 1) = 1 := by
      obtain ⟨t, ht⟩ := hl1
      calc ((ω ^ e) ^ 2) ^ (l ^ f0 l ψ - 1) = (ω ^ (l - 1)) ^ (e * 2 * t) := by
            rw [ht, ← pow_mul, ← pow_mul, ← pow_mul]
            congr 1
            ring
        _ = 1 := by rw [hω, one_pow]
    have hT2 : (th1 l ψ ^ 2) ^ (l ^ f0 l ψ - 1) = 1 := by
      rw [← pow_mul, mul_comm, pow_mul, hth, one_pow]
    refine ⟨hf0, hfour, ?_, hφp, orderOf_dvd_of_pow_eq_one (hφo _ hT hT2), hξp, ?_, ?_⟩
    · exact Odd.of_dvd_nat ((hl.out.odd_of_ne_two hl2).mul hcod) hfd
    · have hfle : f ≤ l * q :=
        Nat.le_of_dvd (Nat.mul_pos hl.out.pos hq0) (dvd_trans hfd (mul_dvd_mul_left l hq))
      have h2 : 2 ^ c2 ψ = 2 * 2 ^ (c2 ψ - 1) := by
        rw [← pow_succ']
        congr 1
        omega
      have hb' : 2 * (l * q * 4 ^ (l ^ f0 l ψ - 1).factorization 2) ≤ 2 * 2 ^ (c2 ψ - 1) := by
        rw [← mul_assoc, ← h2]
        exact hb
      exact le_trans (Nat.mul_le_mul_right _ hfle) (Nat.le_of_mul_le_mul_left hb' two_pos)
    · have hc1 : IsCoprime (-1 : ℤ) ((l * N : ℕ) : ℤ) := isCoprime_one_left.neg_left
      have hc2 : IsCoprime (-1 : ℤ) (N : ℤ) := isCoprime_one_left.neg_left
      have hm1 : IsCoprime (-1 : ℤ) (l : ℤ) := isCoprime_one_left.neg_left
      have e1 := hφ (-1) hc1
      have e2 := hξ (-1) hc2
      rw [pow_app _ _ _ hm1, pow_app _ _ _ hm1, pow_app _ _ _ hc2] at e1
      have hw : (ω ((-1 : ℤ) : ZMod l) ^ e) ^ 2 = 1 := by
        rw [← pow_mul, mul_comm, pow_mul, sq_neg_one, one_pow]
      rw [hw, sq_neg_one, one_mul] at e1
      rw [sq_neg_one, one_mul] at e2
      have h4 : ZMod.χ₄ ((-1 : ℤ) : ZMod 4) = -1 := by
        first
          | decide
          | rfl
          | simp
      have n1 : (-1 : ZMod f) = ((-1 : ℤ) : ZMod f) := by simp
      have n2 : (-1 : ZMod (2 ^ (c2 ψ - 1))) = ((-1 : ℤ) : ZMod (2 ^ (c2 ψ - 1))) := by simp
      rw [n1, n2, e1, e2, h4]
      simp
  · intro a ha
    have haN : IsCoprime a (N : ℤ) :=
      ha.of_isCoprime_of_dvd_right (Int.natCast_dvd_natCast.2 (dvd_mul_left N (l * N)))
    have halN : IsCoprime a ((l * N : ℕ) : ℤ) :=
      ha.of_isCoprime_of_dvd_right (Int.natCast_dvd_natCast.2 (dvd_mul_right (l * N) N))
    have hal : IsCoprime a (l : ℤ) :=
      ha.of_isCoprime_of_dvd_right
        (Int.natCast_dvd_natCast.2 (dvd_trans (dvd_mul_right l N) (dvd_mul_right (l * N) N)))
    have had : IsCoprime a ((f * 2 ^ (c2 ψ - 1) : ℕ) : ℤ) :=
      ha.of_isCoprime_of_dvd_right (Int.natCast_dvd_natCast.2 hdiv)
    obtain ⟨u, hu⟩ := unitOf _ a had
    rw [UpperTheory.V.X.prodX, MulChar.coeToFun_mul, Pi.mul_apply, ← hu,
      DirichletCharacter.changeLevel_eq_cast_of_dvd, DirichletCharacter.changeLevel_eq_cast_of_dvd, hu,
      ZMod.cast_intCast (R := ZMod f) (Dvd.intro _ rfl : f ∣ f * 2 ^ (c2 ψ - 1)) a,
      ZMod.cast_intCast (R := ZMod (2 ^ (c2 ψ - 1)))
        (Dvd.intro_left _ rfl : 2 ^ (c2 ψ - 1) ∣ f * 2 ^ (c2 ψ - 1)) a,
      hφ a halN, hξ a haN, pow_app _ _ _ hal, pow_app _ _ _ hal, pow_app _ _ _ haN]
    ring
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.HcXppOf
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.X

section SlopeTestRemainingChoices
open UpperTheory.V.U3 UpperTheory.V.UnitaryThreeInertia

private def eGb {k : Type} [CommRing k] (a : k) : Gb (k := k) (-2) :=
  (⟨Matrix.single 2 0 a, by
    intro i j h
    fin_cases i <;> fin_cases j <;> first | (exfalso; revert h; decide) | simp⟩ : gw (R := k) (-2))

private theorem eGb_val {k : Type} [CommRing k] (a : k) : (eGb a).val 2 0 = a := by
  show Matrix.single 2 0 a 2 0 = a
  exact Matrix.single_apply_same _ _ _

private theorem gb_ext {k : Type} [CommRing k] {X Y : Gb (k := k) (-2)} (h : X.val 2 0 = Y.val 2 0) : X = Y := by
  have hX : ∀ a b, UpperTheory.V.U3.wt a b ≠ -2 → (X.val : Matrix (Fin 3) (Fin 3) k) a b = 0 := X.2
  have hY : ∀ a b, UpperTheory.V.U3.wt a b ≠ -2 → (Y.val : Matrix (Fin 3) (Fin 3) k) a b = 0 := Y.2
  apply Subtype.ext
  ext a b
  by_cases hab : a = 2 ∧ b = 0
  · obtain ⟨rfl, rfl⟩ := hab
    exact h
  · have hw : UpperTheory.V.U3.wt a b ≠ -2 := by
      revert hab
      fin_cases a <;> fin_cases b <;> decide
    exact (hX a b hw).trans (hY a b hw).symm

private theorem gb_add {k : Type} [CommRing k] (X Y : Gb (k := k) (-2)) : (X + Y).val 2 0 = X.val 2 0 + Y.val 2 0 := rfl
private theorem gb_sub {k : Type} [CommRing k] (X Y : Gb (k := k) (-2)) : (X - Y).val 2 0 = X.val 2 0 - Y.val 2 0 := rfl

private theorem gb_rep {k D : Type} [CommRing k] [Group D] (η : D →* ℤˣ) (Ψ : D →* kˣ) (g : D) (X : Gb (k := k) (-2))
    (c : k) (hc : c * (Ψ g : k) ^ 2 = ((η g : ℤ) : k)) :
    (UnitaryThreeInertia.gRep η Ψ (-2) g X).val 2 0 = c * X.val 2 0 := by
  rw [gRep_val, adRep_baseLift_apply]
  have hw : UpperTheory.V.U3.wt 2 0 = -2 := by decide
  have r0 : Fin.rev (0 : Fin 3) = 2 := rfl
  have r2 : Fin.rev (2 : Fin 3) = 0 := rfl
  rw [hw, r0, r2, zpow_neg, zpow_ofNat]
  have hc' : c = ((η g : ℤ) : k) * (((Ψ g ^ 2)⁻¹ : kˣ) : k) := by
    have h0 : c * (((Ψ g ^ 2 : kˣ)) : k) * (((Ψ g ^ 2)⁻¹ : kˣ) : k) = c :=
      Units.mul_inv_cancel_right _ _
    rw [Units.val_pow_eq_pow_val, hc] at h0
    exact h0.symm
  rw [hc']
  rcases Int.units_eq_one_or (η g) with h1 | h1
  · rw [ite_eq_left h1, h1]
    simp only [Units.val_one, Int.cast_one]
    ring
  · rw [ite_eq_right (by rw [h1]; decide), h1]
    simp only [Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one]
    ring

end SlopeTestRemainingChoices

theorem UpperTheory.V.X.xppOf :
    ∀ {O : Type} [CommRing O] [IsLocalRing O] {G' Γ ι : Type} [Group G'] [TopologicalSpace G'] [IsTopologicalGroup G'] [Group Γ] [TopologicalSpace Γ] (F : UnitaryThreeInertia.Frame O G' Γ ι) (γ : Γ → ResidueField O), (∀ g, γ g * (F.Ψbar g : ResidueField O) ^ 2 = ((F.η g : ℤ) : ResidueField O)) → (∀ z : Γ → ResidueField O, IsLocallyConstant z → (∀ g h, z (g * h) = z g + γ g * z h) → (∀ v, v ≠ F.vl → ∀ s ∈ F.Nv v, z (F.loc v s) = 0) → (∃ m, ∀ s, z (F.loc F.vl s) = γ (F.loc F.vl s) * m - m) → ∃ m, ∀ g, z g = γ g * m - m) → F.Xpp := by
  intro O iR iL G' Γ ι iG iT iTG iΓ iTΓ F γ hγ hmain
  show Subsingleton (F.selmerCohomologyQuotient (-2))
  refine Submodule.Quotient.subsingleton_iff.2 ?_
  rw [eq_top_iff]
  rintro ⟨f, hf⟩ -
  show f ∈ B1 (F.gbar (-2))
  obtain ⟨hZ, hL⟩ := Submodule.mem_inf.1 hf
  obtain ⟨hcont, hcoc⟩ := (mem_Z1_iff_cocycle _ _).1 hZ
  have hZL : ∀ v, F.res1 (-2) v f ∈ Z1 (F.gloc (-2) v) ∧
      (v ≠ F.vl → ∀ s ∈ F.Nv v, F.res1 (-2) v f s = 0) ∧
      (v = F.vl → (-2 : ℤ) < 0 → F.res1 (-2) v f ∈ B1 (F.gloc (-2) v)) ∧
      (v = F.vl → (-2 : ℤ) = 0 → ∀ s ∈ F.Iv v, F.res1 (-2) v f s = 0) :=
    fun v => (Submodule.mem_iInf _).1 hL v
  have hlc : IsLocallyConstant (fun g => (f g).val 2 0) :=
    ((IsLocallyConstant.iff_continuous _).2 hcont).comp
      (fun X : UpperTheory.V.UnitaryThreeInertia.Gb (k := ResidueField O) (-2) => X.val 2 0)
  obtain ⟨m, hm⟩ := hmain (fun g => (f g).val 2 0) hlc
    (by
      intro g h
      show (f (g * h)).val 2 0 = (f g).val 2 0 + γ g * (f h).val 2 0
      rw [hcoc g h, gb_add, gb_rep F.η F.Ψbar g _ (γ g) (hγ g)])
    (by
      intro v hv s hs
      have h0 : f (F.loc v s) = 0 := (hZL v).2.1 hv s hs
      show (f (F.loc v s)).val 2 0 = 0
      rw [h0]
      rfl)
    (by
      obtain ⟨m, hm⟩ := (mem_coboundaries1 _ _).1 ((hZL F.vl).2.2.1 rfl (by norm_num))
      refine ⟨m.val 2 0, fun s => ?_⟩
      have h' : f (F.loc F.vl s) = F.gbar (-2) (F.loc F.vl s) m - m := hm s
      show (f (F.loc F.vl s)).val 2 0 = _
      rw [h', gb_sub, gb_rep F.η F.Ψbar _ _ (γ _) (hγ _)])
  rw [mem_coboundaries1]
  refine ⟨eGb m, fun g => gb_ext ?_⟩
  rw [gb_sub, gb_rep F.η F.Ψbar g _ (γ g) (hγ g), eGb_val]
  exact hm g
end

