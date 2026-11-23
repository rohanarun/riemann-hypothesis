module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0612
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0614
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRetractionMulP
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConvEqOneOfForallPairing
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0415
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0328
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0002
public import Development.AbelianVarietyTheory.Counterexamples.AbelianLawCounterexamples.WeilIsUniqueOfLocal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0566
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0620
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0584
public import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CobOneEqZeroOfConnecting
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0588

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelPairingEq
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev

namespace GlobalTheory.UPel.HT.FinLevSim

def mulSub (O L : Type) [Ring O] [AddCommGroup L] [Module O L] (N : ℕ) : Submodule O L where
  carrier := {x | ∃ y, x = N • y}
  add_mem' := by
    rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
    exact ⟨a + b, (smul_add N a b).symm⟩
  zero_mem' := ⟨0, (smul_zero N).symm⟩
  smul_mem' := by
    rintro c _ ⟨a, rfl⟩
    exact ⟨c • a, smul_comm c N a⟩

theorem finite_quot (O L : Type) [Ring O] [AddCommGroup L] [Module O L] [Module.Finite ℤ L] {N : ℕ}
    (hN : 0 < N) : Finite (L ⧸ mulSub O L N) := by
  have h1 : AddGroup.FG L := Module.Finite.iff_addGroup_fg.1 inferInstance
  have h2 : AddGroup.FG (L ⧸ mulSub O L N) :=
    AddGroup.fg_of_surjective (f := (mulSub O L N).mkQ.toAddMonoidHom) (mulSub O L N).mkQ_surjective
  refine AddCommGroup.finite_of_fg_torsion _ ?_
  intro x
  obtain ⟨x, rfl⟩ := (mulSub O L N).mkQ_surjective x
  rw [isOfFinAddOrder_iff_nsmul_eq_zero]
  refine ⟨N, hN, ?_⟩
  rw [← map_nsmul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  exact ⟨x, rfl⟩

theorem mem_of_dvd {p : ℕ} [Fact p.Prime] (D : Datum p) (r : ℕ) (x : D.La)
    (h : ∀ y, ((p ^ r : ℕ) : ℤ) ∣ D.EF x y) : ∃ y, x = (p ^ r) • y := by
  obtain ⟨e, he, hperf⟩ := D.perfP
  have hN : ((p ^ r : ℕ) : ℤ) ≠ 0 := by
    exact_mod_cast (pow_pos (Fact.out : p.Prime).pos r).ne'
  choose q hq using h
  let f₀ : D.La →ₗ[ℤ] ℤ :=
    { toFun := q
      map_add' := fun a b => mul_left_cancel₀ hN (by rw [mul_add, ← hq, ← hq, ← hq, map_add (f := _)])
      map_smul' := fun c a => mul_left_cancel₀ hN (by
        rw [← hq, map_smul, hq]; simp only [smul_eq_mul, RingHom.id_apply]; ring) }
  obtain ⟨w, hw⟩ := hperf f₀
  have h1 : e • x = (p ^ r) • w := by
    apply D.nondeg
    ext y
    rw [map_nsmul, map_nsmul, hw]
    simp only [LinearMap.smul_apply, nsmul_eq_mul, hq]
    show (e : ℤ) * (((p ^ r : ℕ) : ℤ) * q y) = ((p ^ r : ℕ) : ℤ) * ((e : ℤ) * q y)
    ring
  have hc : IsCoprime (e : ℤ) ((p ^ r : ℕ) : ℤ) := Nat.isCoprime_iff_coprime.2 (he.pow_right r)
  obtain ⟨a, b, hab⟩ := hc
  refine ⟨a • w + b • x, ?_⟩
  have h2 : (e : ℤ) • x = ((p ^ r : ℕ) : ℤ) • w := by rw [natCast_zsmul, natCast_zsmul, h1]
  calc x = (a * (e : ℤ) + b * ((p ^ r : ℕ) : ℤ)) • x := by rw [hab, one_smul]
    _ = (p ^ r) • (a • w + b • x) := by
      rw [add_smul, mul_smul, h2, ← natCast_zsmul, smul_add, smul_smul, smul_smul, smul_smul, mul_comm a,
        mul_comm b]

theorem exists_level_pairing_eq : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (Q : Type) [CommGroup Q] (act : D.O → Q → Q) (r : ℕ) (W : Q → Q → kˣ) (ζ : kˣ), IsPrimitiveRoot ζ (p ^ r) → (∀ a a' b : Q, a ^ (p ^ r) = 1 → a' ^ (p ^ r) = 1 → b ^ (p ^ r) = 1 → W (a * a') b = W a b * W a' b) → (∀ a b : Q, a ^ (p ^ r) = 1 → b ^ (p ^ r) = 1 → W a b * W b a = 1) → (∀ (c : D.O) (a b : Q), a ^ (p ^ r) = 1 → b ^ (p ^ r) = 1 → W (act c a) b = W a (act (D.star c).unop b)) → (∀ a : Q, a ^ (p ^ r) = 1 → (∀ b : Q, b ^ (p ^ r) = 1 → W a b = 1) → a = 1) → ∀ f : D.La → Q, ((∀ x y, f (x + y) = f x * f y) ∧ (∀ (c : D.O) x, f (c • x) = act c (f x)) ∧ (∀ x, f x = 1 ↔ ∃ y, x = (p ^ r) • y) ∧ (∀ g : Q, g ^ (p ^ r) = 1 ↔ ∃ x, f x = g)) → ∃ f' : D.La → Q, ((∀ x y, f' (x + y) = f' x * f' y) ∧ (∀ (c : D.O) x, f' (c • x) = act c (f' x)) ∧ (∀ x, f' x = 1 ↔ ∃ y, x = (p ^ r) • y) ∧ (∀ g : Q, g ^ (p ^ r) = 1 ↔ ∃ x, f' x = g)) ∧ ∀ x y, W (f' x) (f' y) = ζ ^ D.EF x y := by
  intro p _ D k _ _ _ Q _ act r W ζ hζ Wadd Wskew Wadj Wnd f ⟨fadd, flin, fker, fonto⟩
  have hN : 0 < p ^ r := pow_pos (Fact.out : p.Prime).pos r
  haveI := D.finLa
  set K := mulSub D.O D.La (p ^ r) with hK
  haveI : Finite (D.La ⧸ K) := finite_quot D.O D.La hN
  have surj : Function.Surjective K.mkQ := K.mkQ_surjective
  let s : D.La ⧸ K → D.La := Function.surjInv surj
  have hs : ∀ x, K.mkQ (s x) = x := Function.surjInv_eq surj
  have hs' : ∀ x, ∃ y, s (K.mkQ x) = x + (p ^ r) • y := by
    intro x
    have : s (K.mkQ x) - x ∈ K := (Submodule.Quotient.eq K).1 (hs (K.mkQ x))
    obtain ⟨y, hy⟩ := this
    exact ⟨y, by rw [← hy]; abel⟩
  have hmk : ∀ x, K.mkQ x = 0 ↔ ∃ y, x = (p ^ r) • y := fun x => Submodule.Quotient.mk_eq_zero K
  let fb : D.La ⧸ K → Q := fun x => f (s x)
  have hfb : ∀ x, fb (K.mkQ x) = f x := by
    intro x
    obtain ⟨y, hy⟩ := hs' x
    show f (s (K.mkQ x)) = f x
    rw [hy, fadd, (fker _).2 ⟨y, rfl⟩, _root_.mul_one]
  have fbadd : ∀ x y, fb (x + y) = fb x * fb y := by
    intro x y
    obtain ⟨x, rfl⟩ := surj x
    obtain ⟨y, rfl⟩ := surj y
    rw [← map_add (f := _), hfb, hfb, hfb, fadd]
  have fblin : ∀ (c : D.O) x, fb (c • x) = act c (fb x) := by
    intro c x
    obtain ⟨x, rfl⟩ := surj x
    rw [← map_smul, hfb, hfb, flin]
  have fbker : ∀ x, fb x = 1 ↔ x = 0 := by
    intro x
    obtain ⟨x, rfl⟩ := surj x
    rw [hfb, fker, hmk]
  have fbonto : ∀ g : Q, g ^ (p ^ r) = 1 ↔ ∃ x, fb x = g := by
    intro g
    rw [fonto]
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨_, hfb x⟩
    · rintro ⟨x, rfl⟩
      exact ⟨_, rfl⟩
  have fbtor : ∀ x, fb x ^ (p ^ r) = 1 := fun x => (fbonto _).2 ⟨x, rfl⟩
  let E : D.La ⧸ K → D.La ⧸ K → kˣ := fun x y => ζ ^ D.EF (s x) (s y)
  have hζ1 : ∀ z : ℤ, ζ ^ (((p ^ r : ℕ) : ℤ) * z) = 1 := fun z =>
    (hζ.zpow_eq_one_iff_dvd _).2 (dvd_mul_right _ _)
  have hE : ∀ x y, E (K.mkQ x) (K.mkQ y) = ζ ^ D.EF x y := by
    intro x y
    obtain ⟨a, ha⟩ := hs' x
    obtain ⟨b, hb⟩ := hs' y
    show ζ ^ D.EF (s (K.mkQ x)) (s (K.mkQ y)) = _
    have : D.EF (x + (p ^ r) • a) (y + (p ^ r) • b) =
        D.EF x y + ((p ^ r : ℕ) : ℤ) * (D.EF x b + D.EF a (y + (p ^ r) • b)) := by
      rw [map_add D.EF, map_nsmul D.EF, LinearMap.add_apply, LinearMap.smul_apply, map_add (D.EF x),
        map_nsmul (D.EF x), nsmul_eq_mul, nsmul_eq_mul]
      ring
    rw [ha, hb, this, zpow_add, hζ1, _root_.mul_one]
  obtain ⟨ε, u, v, hε1, hε2⟩ := GlobalTheory.T.exists_conj_idempotent_mod_prime_pow p D r
  have hkill : ∀ (c : 𝓞 D.F) (x : D.La ⧸ K), algebraMap (𝓞 D.F) D.O ((p : 𝓞 D.F) ^ r * c) • x = 0 := by
    intro c x
    obtain ⟨x, rfl⟩ := surj x
    rw [← map_smul, hmk]
    refine ⟨algebraMap (𝓞 D.F) D.O c • x, ?_⟩
    rw [map_mul, mul_smul, map_pow, map_natCast, ← Nat.cast_pow, Nat.cast_smul_eq_nsmul]
  have hst : (D.star (algebraMap (𝓞 D.F) D.O ε)).unop = algebraMap (𝓞 D.F) D.O (D.bar ε) := by
    rw [D.star_F, MulOpposite.unop_op]
  have hskew : ∀ x y, D.EF x y + D.EF y x = 0 := by
    intro x y
    have h := D.alt (x + y)
    rw [map_add D.EF, LinearMap.add_apply, map_add (f := _), map_add (f := _), D.alt, D.alt] at h
    linarith
  obtain ⟨g, hg⟩ := GlobalTheory.T.exists_linearEquiv_of_adjoint_skewPairings D.O (fun c => (D.star c).unop) (D.La ⧸ K) k
    (fun x y => W (fb x) (fb y)) E (algebraMap (𝓞 D.F) D.O ε) D.star_star
    (fun c => Algebra.commutes ε c)
    (fun c => by simp only [hst]; exact Algebra.commutes _ c)
    (fun x => by
      simp only [hst]
      rw [← add_smul, ← map_add (f := _), hε1, map_add (f := _), map_one, add_smul, one_smul, hkill, add_zero])
    (fun x => by
      simp only [hst]
      rw [← mul_smul, ← map_mul, hε2, hkill])
    (fun x x' y => by
      simp only [fbadd]
      exact Wadd _ _ _ (fbtor _) (fbtor _) (fbtor _))
    (fun x y => Wskew _ _ (fbtor _) (fbtor _))
    (fun c x y => by
      simp only [fblin]
      exact Wadj _ _ _ (fbtor _) (fbtor _))
    (fun x hx => by
      refine (fbker x).1 (Wnd _ (fbtor _) fun b hb => ?_)
      obtain ⟨y, rfl⟩ := (fbonto b).1 hb
      exact hx y)
    (fun x x' y => by
      obtain ⟨x, rfl⟩ := surj x
      obtain ⟨x', rfl⟩ := surj x'
      obtain ⟨y, rfl⟩ := surj y
      rw [← map_add (f := _), hE, hE, hE, map_add (f := _), LinearMap.add_apply, zpow_add])
    (fun x y => by
      obtain ⟨x, rfl⟩ := surj x
      obtain ⟨y, rfl⟩ := surj y
      rw [hE, hE, ← zpow_add, hskew, zpow_zero])
    (fun c x y => by
      obtain ⟨x, rfl⟩ := surj x
      obtain ⟨y, rfl⟩ := surj y
      rw [← map_smul, ← map_smul, hE, hE, D.adj])
    (fun x hx => by
      obtain ⟨x, rfl⟩ := surj x
      refine (hmk x).2 (mem_of_dvd D r x fun y => ?_)
      have := hx (K.mkQ y)
      rw [hE] at this
      exact (hζ.zpow_eq_one_iff_dvd _).1 this)
  refine ⟨fun x => fb (g (K.mkQ x)), ⟨fun x y => ?_, fun c x => ?_, fun x => ?_, fun q => ?_⟩, fun x y => ?_⟩
  · simp only [map_add (f := _), fbadd]
  · simp only [map_smul, fblin]
  · simp only []
    rw [fbker, g.map_eq_zero_iff, hmk]
  · rw [fbonto]
    constructor
    · rintro ⟨x, rfl⟩
      obtain ⟨y, hy⟩ := surj (g.symm x)
      exact ⟨y, by simp only []; rw [hy, g.apply_symm_apply]⟩
    · rintro ⟨x, rfl⟩
      exact ⟨_, rfl⟩
  · exact (hg _ _).trans (hE x y)

end GlobalTheory.UPel.HT.FinLevSim
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsQuotPDivGroup
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Coalgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.HTPair
open scoped TensorProduct

namespace GlobalTheory.HTPair

theorem exists_quotPDivGroup : ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [IsDomain O]
    [IsLocalRing O] (G : PDivGroup p O) (τ : QuotTower G), ∃ (H : PDivGroup p O)
    (q : ∀ m, τ.B m →ₐc[O] H.A m), (∀ m, Function.Surjective (q m)) ∧
    (∀ m, RingHom.ker (q m) = torsionIdeal (R := O) (A := τ.B m) (p ^ m)) ∧
    ∀ m b, H.res m (q (m + 1) b) = q m (τ.r m b) := by
  intro p _ O _ _ _ G τ
  have existsHopfQuotient :
      ∀ (O : Type) [CommRing O] (B : Type) [CommRing B] [HopfAlgebra O B] [IsCocomm O B] (n : ℕ),
        ∃ (D : Type) (_ : CommRing D) (_ : HopfAlgebra O D) (_ : IsCocomm O D) (π : B →ₐc[O] D),
          Function.Surjective π ∧ RingHom.ker π = torsionIdeal (R := O) (A := B) n := by
    intro O _ B _ _ _ n
    let f : B →ₐc[O] B := mulBy (R := O) (A := B) n
    let I := kerIdeal f
    let q : B →ₐ[O] B ⧸ I := Ideal.Quotient.mkₐ O I
    have hI : I.IsHopfIdeal O := by
      refine { toIsCoideal := ?_, antipode_mem := ?_ }
      · refine { counit_eq_zero := ?_, map_mkQ_comul_eq_zero := ?_ }
        · intro x hx
          exact (kerIdeal_le_ker_iff f (Bialgebra.counitAlgHom O B)).2 (fun c => by simp) hx
        · intro x hx
          have hqf : ∀ c : B, q (f c) = algebraMap O (B ⧸ I) (counit (R := O) c) :=
            (kerIdeal_le_ker_iff f q).1 fun _ hc => Ideal.Quotient.eq_zero_iff_mem.2 hc
          have hcomp : q.toLinearMap ∘ₗ (f : B →ₗ[O] B) =
              Algebra.linearMap O (B ⧸ I) ∘ₗ counit := LinearMap.ext hqf
          let Φ := (Algebra.TensorProduct.map q q).comp (Bialgebra.comulAlgHom O B)
          have hΦ : I ≤ RingHom.ker Φ := by
            refine Ideal.map_le_iff_le_comap.2 fun c hc => ?_
            have hc' : counit (R := O) c = 0 := hc
            change TensorProduct.map q.toLinearMap q.toLinearMap (comul (f c)) = 0
            rw [← CoalgHomClass.map_comp_comul_apply, ← LinearMap.comp_apply,
              ← TensorProduct.map_comp, hcomp]
            have hsplit : TensorProduct.map (Algebra.linearMap O (B ⧸ I) ∘ₗ counit)
                (Algebra.linearMap O (B ⧸ I) ∘ₗ counit) =
                TensorProduct.map (Algebra.linearMap O (B ⧸ I))
                  (Algebra.linearMap O (B ⧸ I) ∘ₗ counit) ∘ₗ
                  LinearMap.rTensor B (counit (R := O) (A := B)) := by
              rw [LinearMap.rTensor, ← TensorProduct.map_comp, LinearMap.comp_id]
            rw [hsplit, LinearMap.comp_apply, Coalgebra.rTensor_counit_comul, TensorProduct.map_tmul]
            simp [hc']
          exact hΦ hx
      · have hle : I ≤ I.comap (HopfAlgebra.antipodeAlgHom O B) := by
          refine Ideal.map_le_iff_le_comap.2 fun c hc => ?_
          have hc' : counit (R := O) c = 0 := hc
          change HopfAlgebra.antipode O (f c) ∈ I
          rw [← GlobalTheory.bialgHom_map_antipode]
          exact Ideal.mem_map_of_mem (f : B →ₐ[O] B) (by simp [RingHom.mem_ker, hc'])
        exact fun _ hx => hle hx
    let π : B →ₐc[O] B ⧸ I := Bialgebra.Quotient.mkBialgHom I
    have hπ : Function.Surjective π := Ideal.Quotient.mk_surjective
    have cocomm : IsCocomm O (B ⧸ I) :=
      { comm_comp_comul := LinearMap.ext fun b => by
          obtain ⟨a, rfl⟩ := hπ b
          have h : ∀ t : B ⊗[O] B,
              TensorProduct.comm O (B ⧸ I) (B ⧸ I)
                  (TensorProduct.map (π : B →ₗ[O] B ⧸ I) (π : B →ₗ[O] B ⧸ I) t) =
              TensorProduct.map (π : B →ₗ[O] B ⧸ I) (π : B →ₗ[O] B ⧸ I)
                (TensorProduct.comm O B B t) := by
            intro t
            induction t with
            | add x y hx hy => simp only [map_add (f := _), hx, hy]
            | tmul x y => simp
          change TensorProduct.comm O (B ⧸ I) (B ⧸ I) (comul (π a)) = comul (π a)
          rw [← CoalgHomClass.map_comp_comul_apply π a, h, comm_comul] }
    exact ⟨B ⧸ I, inferInstance, inferInstance,
      cocomm, π, hπ,
      Ideal.ext fun _ => Ideal.Quotient.eq_zero_iff_mem⟩
  have hex := fun m => existsHopfQuotient O (τ.B m) (p ^ m)
  choose D iR iH iC q hq hk using hex
  letI := iR
  letI := iH
  letI := iC
  have hB1 : ∀ m (x : PrimeSpectrum O),
      fibreDim (τ.B m ⧸ torsionIdeal (R := O) (A := τ.B m) (p ^ m)) x = p ^ (m * G.height) := by
    intro m x
    have h := GlobalTheory.T.torsion_fibreDim_quotient_pDivGroupLevel p O G 1 m le_rfl (τ.B m)
    rw [show 1 + m = m + 1 from Nat.add_comm 1 m] at h
    exact h (τ.j m) (τ.ρ m) (τ.ρ_j m) (τ.tors_le m) x
  have hB2 : ∀ m (x : PrimeSpectrum O),
      fibreDim (τ.B (m + 1) ⧸ torsionIdeal (R := O) (A := τ.B (m + 1)) (p ^ m)) x = p ^ (m * G.height) := by
    intro m x
    have h := GlobalTheory.T.torsion_fibreDim_quotient_pDivGroupLevel p O G 2 m (by norm_num) (τ.B (m + 1))
    rw [show 2 + m = m + 1 + 1 by omega] at h
    exact h (τ.j (m + 1)) (τ.ρ (m + 1)) (τ.ρ_j (m + 1)) (τ.tors_le (m + 1)) x
  haveI hfin : ∀ m, Module.Finite O (D m) := fun m =>
    Module.Finite.of_surjective (q m : τ.B m →ₗ[O] D m) (hq m)
  have hD : ∀ m (x : PrimeSpectrum O), fibreDim (D m) x = p ^ (m * G.height) := by
    intro m x
    have hk' : RingHom.ker (q m : τ.B m →ₐ[O] D m) = torsionIdeal (R := O) (A := τ.B m) (p ^ m) := hk m
    have e := ((Ideal.quotientEquivAlgOfEq O hk').symm.trans
      (Ideal.quotientKerAlgEquivOfSurjective (f := (q m : τ.B m →ₐ[O] D m)) (hq m))).toLinearEquiv
    rw [← hB1 m x]
    exact (fibreDim_congr e x).symm
  have hPR := fun m => _root_.GlobalTheory.ConstFibreFree.projective_and_rankAtStalk_of_fibreDim O (D m) (p ^ (m * G.height)) (hD m)
  haveI hproj : ∀ m, Module.Projective O (D m) := fun m => (hPR m).1
  have hle : ∀ m, RingHom.ker (q (m + 1)) ≤ RingHom.ker ((q m).comp (τ.r m)) := by
    intro m b hb
    rw [hk] at hb
    have h1 : τ.r m b ∈ torsionIdeal (R := O) (A := τ.B m) (p ^ (m + 1)) := by
      rw [← map_torsionIdeal (τ.r_surjective m)]
      exact Ideal.mem_map_of_mem (τ.r m : τ.B (m + 1) →ₐ[O] τ.B m) hb
    have h2 : τ.r m b ∈ RingHom.ker (q m) := by
      rw [hk]
      exact torsionIdeal_le_of_dvd (pow_dvd_pow p (Nat.le_succ m)) h1
    rw [RingHom.mem_ker] at h2 ⊢
    exact h2
  let res := fun m => liftSurj (q (m + 1)) (hq (m + 1)) ((q m).comp (τ.r m)) (hle m)
  have hres : ∀ m b, res m (q (m + 1) b) = q m (τ.r m b) := fun m b => liftSurj_apply ..
  have hres_surj : ∀ m, Function.Surjective (res m) := by
    intro m d
    obtain ⟨c, rfl⟩ := hq m d
    obtain ⟨b, rfl⟩ := τ.r_surjective m c
    exact ⟨_, hres m b⟩
  have hker : ∀ m, RingHom.ker (res m) = torsionIdeal (R := O) (A := D (m + 1)) (p ^ m) := by
    intro m
    refine ker_eq_of_fibreDim_eq (res m : D (m + 1) →ₐ[O] D m) (hres_surj m) _ ?_ fun x => ?_
    · rw [← map_torsionIdeal (hq (m + 1))]
      refine Ideal.map_le_iff_le_comap.2 fun b hb => ?_
      rw [Ideal.mem_comap, RingHom.mem_ker]
      change res m (q (m + 1) b) = 0
      rw [hres, ← RingHom.mem_ker, hk, ← map_torsionIdeal (τ.r_surjective m)]
      exact Ideal.mem_map_of_mem (τ.r m : τ.B (m + 1) →ₐ[O] τ.B m) hb
    · let φ : τ.B (m + 1) →ₐ[O] D (m + 1) ⧸ torsionIdeal (R := O) (A := D (m + 1)) (p ^ m) :=
        (Ideal.Quotient.mkₐ O _).comp (q (m + 1) : τ.B (m + 1) →ₐ[O] D (m + 1))
      have hφ : Function.Surjective φ :=
        (Ideal.Quotient.mkₐ_surjective O _).comp (hq (m + 1))
      have hkφ : RingHom.ker φ = torsionIdeal (R := O) (A := τ.B (m + 1)) (p ^ m) := by
        ext b
        rw [RingHom.mem_ker]
        change Ideal.Quotient.mk _ (q (m + 1) b) = 0 ↔ _
        rw [Ideal.Quotient.eq_zero_iff_mem, ← map_torsionIdeal (hq (m + 1))]
        constructor
        · intro hb
          obtain ⟨c, hc, e⟩ := (Ideal.mem_map_iff_of_surjective
            (q (m + 1) : τ.B (m + 1) →ₐ[O] D (m + 1)) (hq (m + 1))).1 hb
          have h3 : b - c ∈ RingHom.ker (q (m + 1)) := by
            rw [RingHom.mem_ker, map_sub, sub_eq_zero]
            exact e.symm
          rw [hk] at h3
          have h4 := torsionIdeal_le_of_dvd (R := O) (A := τ.B (m + 1))
            (pow_dvd_pow p (Nat.le_succ m)) h3
          simpa using Ideal.add_mem _ h4 hc
        · intro hb
          exact Ideal.mem_map_of_mem (q (m + 1) : τ.B (m + 1) →ₐ[O] D (m + 1)) hb
      have e := ((Ideal.quotientEquivAlgOfEq O hkφ).symm.trans
        (Ideal.quotientKerAlgEquivOfSurjective hφ)).toLinearEquiv
      rw [hD, ← hB2 m x]
      exact (fibreDim_congr e x).symm
  let H : PDivGroup p O :=
    { height := G.height
      A := D
      commRing := iR
      hopf := iH
      cocomm := iC
      finite := hfin
      projective := hproj
      rank_eq := fun m x => (hPR m).2 x
      res := res
      res_surjective := hres_surj
      ker_res := hker }
  exact ⟨H, q, hq, hk, hres⟩

end GlobalTheory.HTPair
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueFullLevel
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FullLevel

open AlgebraicGeometry CategoryTheory _root_.CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem weilIs_unitOn_unique {S : Scheme.{0}} (G : Over S) [GrpObj G] {L : LB G.left} (hL : L.IsLB)
    {k : Type} [Field k] (x : Sp k ⟶ S) (n : ℤ) (g g' : Over.mk x ⟶ G) (c c' : kˣ)
    (h : Out.WeilIs G L n g g' (unitOn c)) (h' : Out.WeilIs G L n g g' (unitOn c')) : c = c' := by
  have hU : Subsingleton (Sp k) := by
    show Subsingleton (PrimeSpectrum k); infer_instance
  obtain ⟨p⟩ : Nonempty (Sp k) := by
    show Nonempty (PrimeSpectrum k); infer_instance
  have hp : ∀ V : (Over.mk x).left.Opens, p ∈ V → V = ⊤ := by
    intro V hV
    apply TopologicalSpace.Opens.ext
    ext y
    exact ⟨fun _ => trivial, fun _ => (Subsingleton.elim (α := Sp k) p y) ▸ hV⟩
  have H := GlobalTheory.ThetaGroupTest.weilIs_unique_of_local p hp hL h h'
  have hinj : Function.Injective (Units.map ((⊤ : (Over.mk x).left.Opens).ι.appTop.hom.toMonoidHom)) := by
    apply Units.map_injective
    haveI : IsIso ((⊤ : (Over.mk x).left.Opens).ι.app ⊤) := Scheme.Hom.isIso_app _ _ (by simp)
    exact (ConcreteCategory.bijective_of_isIso ((⊤ : (Over.mk x).left.Opens).ι.app ⊤)).1
  have H2 : unitOn c = unitOn c' := hinj H
  unfold unitOn at H2
  have hinj2 : Function.Injective (Units.map (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom.toMonoidHom) := by
    apply Units.map_injective
    exact (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of k)).inv).1
  exact hinj2 H2

theorem exists_unique_fullLevel {D : Datum H} {l : Level H} {B : Type} [CommRing B] {b : Base l B}
    {S : Scheme.{0}} {s : S ⟶ Sp B} (o : Obj D l b s) (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S)
    (β : B →+* k) (hx : x ≫ s = spMap β) (z : kˣ) (hz : IsPrimitiveRoot z l.M')
    (hzA : (z : k) ^ (l.M' / l.A) = β b.ζ) :
    ∃! ev : D.La → (Over.mk x ⟶ o.t.G),
      IsSympLevel D (fun a g => g ≫ o.t.act.act a)
          (fun n g g' c => Out.WeilIs o.t.G o.t.PP.L n g g' (unitOn c)) l.M' z ev ∧
        Induces l (fun a => toUnit _ ≫ o.etaA a) (fun a => toUnit _ ≫ o.eta a) ev := by
  obtain ⟨-, I, hIA, hetaA, heta⟩ := o.geom k x β hx
  have hzA' : z ^ (l.M' / l.A) = I.ζ l.A := Units.ext (by rw [Units.val_pow_eq_pow_val, hzA, hIA])
  obtain ⟨ev, hev, hA, hM⟩ := _root_.GlobalTheory.FullLevel.exists_sympLevel_of_tate l I hz hzA'
  have hi : Induces l (fun a => toUnit _ ≫ o.etaA a) (fun a => toUnit _ ≫ o.eta a) ev :=
    ⟨fun a => (hA a).trans (hetaA a).symm, fun a ha => (hM a ha).trans (heta a ha).symm⟩
  refine ⟨ev, ⟨hev, hi⟩, ?_⟩
  rintro ev' ⟨h1, h2⟩
  have := GlobalTheory.T.isFullSymplecticLevelStructure_unique_of_levels l (fun g g' c c' => weilIs_unitOn_unique o.t.G o.t.PP.isLB x _ g g' c c') hz
    hev hi h1 h2
  exact this.symm

end GlobalTheory.FullLevel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueLieOfAdditive
section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

namespace GlobalTheory.LieOfAdditive

theorem existsUnique_lie_of_additive : ∀ (p : ℕ) (O : Type) [CommRing O] [IsAdicComplete (Ideal.span {(p : O)}) O] (G : PDivGroup p O) (b : ∀ n, G.A n), (∀ n, ∃ z, cobOne O (G.A n) (b n) = (p : O) ^ n • z) → (∀ n, ∃ z, b (n + 1) = G.mulP n (b n) + (p : O) ^ n • z) → ∃! l : G.dual.Lie, ∀ (n : ℕ) (w : G.dual.omega) (φ : CartierDual O (G.A n)), dUnit (R := O) φ = w.1 n → (p : O) ^ n ∣ l w - φ (b n) := by
  intro p O _ _ G b hb hc
  have hu : ∀ n, ∃ u : Cot O (CartierDual O (G.A n)) →ₗ[O] O ⧸ Ideal.span {((p : O)) ^ n},
      ∀ φ : CartierDual O (G.A n), u (dUnit (R := O) φ) = Ideal.Quotient.mk _ (φ (b n)) := fun n => by
    obtain ⟨z, hz⟩ := hb n
    exact GlobalTheory.T.exists_cartierDual_tangent_of_coboundaryOne_eq_smul O (G.A n) ((p : O) ^ n) (b n) z hz
  choose u hu using hu
  let U : ∀ n : ℕ, G.dual.omega →ₗ[O] O ⧸ Ideal.span {((p : O)) ^ n} := fun n =>
    (u n).comp ((LinearMap.proj n).comp G.dual.omegaSub.subtype)
  have hU : ∀ n (w : G.dual.omega) (φ : CartierDual O (G.A n)), dUnit (R := O) φ = w.1 n →
      U n w = Ideal.Quotient.mk _ (φ (b n)) := by
    intro n w φ h
    show u n (w.1 n) = _
    rw [← h, hu]
  have key : ∀ n (w : G.dual.omega) (x : O), U (n + 1) w = Ideal.Quotient.mk _ x →
      U n w = Ideal.Quotient.mk _ x := by
    intro n w x hx
    obtain ⟨φ, hφ⟩ := AugCot.d_surjective _ (w.1 (n + 1))
    have h1 : dUnit (R := O) (CartierDual.map (G.mulP n) φ) = w.1 n := by
      rw [← w.2 n, ← hφ]; exact (cotMap_d _ _).symm
    rw [hU n w _ h1, CartierDual.map_apply]
    rw [hU (n + 1) w φ hφ] at hx
    obtain ⟨z, hz⟩ := hc n
    rw [Ideal.Quotient.eq, Ideal.mem_span_singleton] at hx ⊢
    rw [hz, map_add (f := _), map_smul, smul_eq_mul] at hx
    obtain ⟨k, hk⟩ := hx
    exact ⟨(p : O) * k - φ z, by linear_combination hk⟩
  obtain ⟨l, hl, huniq⟩ := _root_.GlobalTheory.PDiv.exists_unique_dual_of_compatible_mod_pow O G.dual.omega (p : O) U key
  refine ⟨l, fun n w φ h => ?_, fun l' hl' => huniq l' fun n w => ?_⟩
  · have := (hl n w).trans (hU n w φ h)
    rwa [Ideal.Quotient.eq, Ideal.mem_span_singleton] at this
  · obtain ⟨φ, hφ⟩ := AugCot.d_surjective _ (w.1 n)
    rw [hU n w φ hφ, Ideal.Quotient.eq, Ideal.mem_span_singleton]
    exact hl' n w φ hφ

end GlobalTheory.LieOfAdditive
end

