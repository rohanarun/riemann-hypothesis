module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0015
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
public import Formalism.SatakeDualWeyl.KpqSubgroupCompact
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0136
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0141
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0143
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0157
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0123
public import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.FdOfCharts
public import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0016
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.AlternatingFormStandardHermitian
public import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.RepComb
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.ThDistC
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.PeriodLatticeFinitelyGenerated
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.SelfDualLatticeNorms.SelfDualComap
public import Development.AutomorphicArithmetic.CyclotomicBounds.Bundle0002
public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Formalism.FrobeniusOrbits.HostCorollaries
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FinrankMaxUnramifiedSubfieldPadicFinExtPos
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0159
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0111
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0066
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0128
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0140

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChainInnerStepIntertwinesMatchedHecke
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ChainStepHecke

theorem haar_fd {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (hM : R.IsModels) (t : T) (j : ℕ)
    (hj : j < D.R.m) :
    (R.νY t j).IsHaarMeasure ∧ IsFundamentalDomain (GQ (Yc D j)) (R.fdY t j) (R.νY t j) := by
  by_cases h : j + 1 < D.R.m
  · have := hM.νY t j h
    exact ⟨this.1.1, this.2⟩
  · obtain rfl : j = D.R.m - 1 := by omega
    have := hM.νY' t
    exact ⟨this.1.1, this.2⟩

theorem step_hk : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Chain.LiftInteg D → Core R F → SchurAll R → ∀ t P k, Good R t P → k + 1 < D.R.m → VacFix R.ψ (R.ωY t k) P → ∀ cS cT, Match R.ψ (R.ωY t k) P cS (dualC cT) → ∀ U U' : R.CC t (k + 1), (∀ v, U'.1 v = hk _ P cT (U.1 v)) → ∀ v, (R.ioY t k U').1 v = hk _ P cS ((R.ioY t k U).1 v) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hI hC hS t P k hG hkk hF cS cT hM U U' hU v
  classical
  have hθ : IsInfFam R.θ := hC.models.inf
  have hN := ((_root_.GlobalTheory.GoodPrimes.good_primes R F hC.lev).2.1 t P hG).1
  have hio := hC.chain.ioY t k (by omega)
  obtain ⟨hνH, hνF⟩ := haar_fd R hC.models t (k + 1) hkk
  obtain ⟨hμH, hμF⟩ := haar_fd R hC.models t k (by omega)
  have lo : ∀ j, j < D.R.m → (∀ κ ∈ GlobalTheory.Hk3.hyp (Yc D j) P, κ ∈ levG _ (R.βY j) (R.datYt t j R.triv) ∧
        levChi _ (R.βY j) (R.datYt t j R.triv) κ = 1) ∧
      ∀ c, ∀ U ∈ Mult R.θ (R.MY j) (levS _ (R.βY j) (R.datYt t j R.triv)) (levChi _ (R.βY j) (R.datYt t j R.triv)),
        postOn (R.MY j) (hk _ P c) U ∈ Mult R.θ (R.MY j) (levS _ (R.βY j) (R.datYt t j R.triv)) (levChi _ (R.βY j) (R.datYt t j R.triv)) := by
    intro j hj
    obtain ⟨c, hb⟩ := hC.lev.βY j hj
    have h := _root_.GlobalTheory.LevOp.level_operators (Yc D j) (R.βY j) (R.ΛY j) _ (R.datYt t j R.triv) hb P (by
      rw [Nat.cast_pow]
      exact fun h => hN (P.isPrime.mem_of_pow_mem _ h)) hG
    exact ⟨h.1, fun c U hU => h.2.2.2.2 _ R.θ (R.MY j) c hθ U hU⟩

  have hwm := (lo k (by omega)).2 cS _ ((mem_multT R.θ _ _ _ _).1 (R.ioY t k U).2)
  let w : R.CC t k := ⟨PiTensorProduct.lift (postOn (R.MY k) (hk _ P cS) (PiTensorProduct.lift.symm (R.ioY t k U).1)),
    (mem_multT R.θ _ _ _ _).2 (by simpa using hwm)⟩
  have hw : ∀ x, w.1 x = hk _ P cS ((R.ioY t k U).1 x) := by
    intro x
    have : w.1 = (hk _ P cS) ∘ₗ (R.ioY t k U).1 := PiTensorProduct.ext (MultilinearMap.ext fun y => by
      simp [w, postOn_apply])
    rw [this]; rfl
  have hmap := (GlobalTheory.MultMem.mem_mult_iff _ _ _ _ _ _ _ _).1 ((mem_multT R.θ _ _ _ _).1 U.2)
  have key : ∀ φ x, (R.ioY t k U').1 (R.ItY k φ (PiTensorProduct.tprod ℂ x)) = w.1 (R.ItY k φ (PiTensorProduct.tprod ℂ x)) := by
    intro φ x
    have hvac := (_root_.GlobalTheory.VacGood.fock_vacua_good R F hC t P hG).1 k hkk φ
    have e' : (R.ioY t k U').1 (R.ItY k φ (PiTensorProduct.tprod ℂ x)) =
        Lift.liftInt (R.νY t (k + 1)) (R.fdY t (k + 1)) (thetaKO (R.ωY t k)) (R.ptY t k φ) (U'.1 (PiTensorProduct.tprod ℂ x)) :=
      funext fun g => (hio.eq U' φ _ g).symm
    have e : (R.ioY t k U).1 (R.ItY k φ (PiTensorProduct.tprod ℂ x)) =
        Lift.liftInt (R.νY t (k + 1)) (R.fdY t (k + 1)) (thetaKO (R.ωY t k)) (R.ptY t k φ) (U.1 (PiTensorProduct.tprod ℂ x)) :=
      funext fun g => (hio.eq U φ _ g).symm
    have haut : IsAutFunSm R.θ _ (U.1 (PiTensorProduct.tprod ℂ x)) := by simpa using hmap.aut x
    have hcusp : IsCuspFun _ (U.1 (PiTensorProduct.tprod ℂ x)) := by simpa using hmap.cusp x
    have hlev : ∀ κ ∈ levS _ (R.βY (k + 1)) (R.datYt t (k + 1) R.triv), ∀ g, U.1 (PiTensorProduct.tprod ℂ x) (g * κ) =
        levChi _ (R.βY (k + 1)) (R.datYt t (k + 1) R.triv) κ * U.1 (PiTensorProduct.tprod ℂ x) g := by
      simpa using hmap.lev x
    rw [hw, e', e, hU]
    refine _root_.GlobalTheory.ThetaIntHecke.liftInt_hk R.ψ _ _ _ _ (R.ωY t k) P (hC.chain.ωY t k hkk) _ _ hνH hνF hF cS cT hM _ hvac _ haut.left ?_ ?_
    · intro κ hκ h
      obtain ⟨h1, h2⟩ := (lo (k + 1) hkk).1 κ hκ
      rw [hlev κ h1, h2, one_mul]
    · intro g y hy
      refine hI _ _ R.θ R.ψ _ _ (R.ωY t k) hθ (hC.chain.ωY t k hkk) _ _ hνH hνF _ (rTr _ y (U.1 (PiTensorProduct.tprod ℂ x))) hvac.1
        (GlobalTheory.SphericalOps.isAutFunSm_rTr hy haut) ?_ g
      intro r C hC' μ 𝓕 hμ h𝓕 g'
      simp only [rTr, mul_assoc]
      exact hcusp r C hC' μ 𝓕 hμ h𝓕 (g' * y)
  obtain ⟨φ, x, hx⟩ : ∃ φ x, R.ItY k φ (PiTensorProduct.tprod ℂ x) ≠ 0 := by
    by_contra h
    push_neg at h
    refine (hC.chain.ItY t k hkk).ne (LinearMap.ext fun φ => PiTensorProduct.ext (MultilinearMap.ext fun x => ?_))
    simpa using h φ x
  have h0 := GlobalTheory.multT_eq_zero_of_apply_eq_zero R.θ (R.MY k) _ _ _ _ hθ hμH hμF (hS.1 t k (by omega)) (R.ioY t k U' - w).1 (R.ioY t k U' - w).2 _ hx
    (by simp [key φ x])
  have h1 : (R.ioY t k U').1 = w.1 := sub_eq_zero.1 h0
  rw [h1, hw]

end GlobalTheory.ChainStepHecke
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CommonRepresentativesPeriodLatticeHalves
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F GlobalTheory.TwU TensorProduct
open Formalism.L2.Th1.H Formalism.L2.KerInert.RepComb

noncomputable section

namespace GlobalTheory.CommonReps

def RepsIn {G : Type} [AddCommGroup G] (X Y : AddSubgroup G) (S : Finset G) : Prop :=
  (∀ x ∈ S, x ∈ Y) ∧ (∀ x ∈ S, ∀ y ∈ S, x - y ∈ X → x = y) ∧ ∀ y ∈ Y, ∃ x ∈ S, y - x ∈ X

theorem isReps_map {G V : Type} [AddCommGroup G] [AddCommGroup V] [Module ℂ V] [DecidableEq V] (f : G →+ V)
    (hf : Function.Injective f) {X Y : AddSubgroup G} {S : Finset G} (h : RepsIn X Y S) :
    IsReps (X.map f) (Y.map f) (S.image f) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · intro v hv
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hv
    exact ⟨x, h1 x hx, rfl⟩
  · intro v hv w hw hvw
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hv
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hw
    obtain ⟨m, hm, hme⟩ := hvw
    rw [← map_sub] at hme
    rw [h2 x hx y hy (hf hme ▸ hm)]
  · rintro _ ⟨y, hy, rfl⟩
    obtain ⟨x, hx, hyx⟩ := h3 y hy
    exact ⟨f x, Finset.mem_image_of_mem f hx, ⟨y - x, hyx, map_sub f y x⟩⟩

theorem repsIn_preimage {G V : Type} [AddCommGroup G] [AddCommGroup V] [Module ℂ V] (f : G →+ V)
    (hf : Function.Injective f) {X Y : AddSubgroup G} {T : Finset V} (h : IsReps (X.map f) (Y.map f) T) :
    RepsIn X Y (T.preimage f hf.injOn) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨y, hy, hyx⟩ := h1 (f x) (Finset.mem_preimage.1 hx)
    exact hf hyx ▸ hy
  · intro x hx y hy hxy
    exact hf (h2 _ (Finset.mem_preimage.1 hx) _ (Finset.mem_preimage.1 hy) ⟨x - y, hxy, map_sub f x y⟩)
  · intro y hy
    obtain ⟨v, hv, hyv⟩ := h3 (f y) ⟨y, hy, rfl⟩
    obtain ⟨x, -, rfl⟩ := h1 v hv
    refine ⟨x, Finset.mem_preimage.2 hv, ?_⟩
    obtain ⟨m, hm, hme⟩ := hyv
    rw [← map_sub] at hme
    exact hf hme ▸ hm

theorem repsIn_move {R G : Type} [CommRing R] [AddCommGroup G] [Module R G] [DecidableEq G]
    (X Y X₀ Y₀ : Submodule R G) (g c k : R) (hg : g = 1 + c * k)
    (hY : ∀ y ∈ Y, g • y ∈ Y₀) (hY₀ : ∀ y ∈ Y₀, g • y ∈ Y) (hX : ∀ x ∈ X, g • x ∈ X₀) (hX₀ : ∀ x ∈ X₀, g • x ∈ X)
    (hcY : ∀ y ∈ Y, c • y ∈ X) (hcY₀ : ∀ y ∈ Y₀, c • y ∈ X₀) {S₀ : Finset G}
    (hS : RepsIn X₀.toAddSubgroup Y₀.toAddSubgroup S₀) :
    RepsIn X.toAddSubgroup Y.toAddSubgroup (S₀.image (g • ·)) := by
  obtain ⟨h1, h2, h3⟩ := hS
  have hgg : ∀ z : G, z = g • g • z - (2 * k + c * k * k) • (c • z) := by
    intro z
    rw [smul_smul, smul_smul, ← sub_smul, hg]
    have : (1 + c * k) * (1 + c * k) - (2 * k + c * k * k) * c = 1 := by ring
    rw [this, one_smul]
  refine ⟨?_, ?_, ?_⟩
  · intro v hv
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hv
    exact hY₀ x (h1 x hx)
  · intro v hv w hw hvw
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hv
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hw
    have hxy : x - y ∈ Y₀ := Y₀.sub_mem (h1 x hx) (h1 y hy)
    have e1 : g • g • (x - y) ∈ X₀ := by
      rw [smul_sub g x y]; exact hX _ hvw
    have e2 : x - y ∈ X₀ := by
      rw [hgg (x - y)]
      exact X₀.sub_mem e1 (X₀.smul_mem _ (hcY₀ _ hxy))
    rw [h2 x hx y hy e2]
  · intro y hy
    obtain ⟨x, hx, hyx⟩ := h3 (g • y) (hY y hy)
    refine ⟨g • x, Finset.mem_image_of_mem _ hx, ?_⟩
    have e : y - g • x = g • (g • y - x) - (2 * k + c * k * k) • (c • y) := by
      conv_lhs => rw [hgg y]
      rw [smul_sub]; abel
    rw [e]
    exact X.sub_mem (hX₀ _ hyx) (X.smul_mem _ (hcY y hy))

theorem common_reps_of {R G V κ : Type} [CommRing R] [AddCommGroup G] [Module R G] [AddCommGroup V] [Module ℂ V]
    (f : G →+ V) (hf : Function.Injective f) (g c k : R) (hg : g = 1 + c * k)
    (X Y : κ → Submodule R G) (X₀ Y₀ : Submodule R G)
    (hY : ∀ i, ∀ y ∈ Y i, g • y ∈ Y₀) (hY₀ : ∀ i, ∀ y ∈ Y₀, g • y ∈ Y i) (hX : ∀ i, ∀ x ∈ X i, g • x ∈ X₀)
    (hX₀ : ∀ i, ∀ x ∈ X₀, g • x ∈ X i) (hcY : ∀ i, ∀ y ∈ Y i, c • y ∈ X i) (hcY₀ : ∀ y ∈ Y₀, c • y ∈ X₀)
    (hidx : relIdx (X₀.toAddSubgroup.map f) (Y₀.toAddSubgroup.map f) ≠ 0) :
    ∃ S : Finset V, ∀ i, IsReps ((X i).toAddSubgroup.map f) ((Y i).toAddSubgroup.map f) S := by
  classical
  have h0 := repsIn_preimage f hf (Formalism.L2.Ker.repsOf_spec _ _ hidx)
  exact ⟨(((Formalism.L2.Ker.repsOf _ _).preimage f hf.injOn).image (g • ·)).image f, fun i =>
    isReps_map f hf (repsIn_move (X i) (Y i) X₀ Y₀ g c k hg (hY i) (hY₀ i) (hX i) (hX₀ i) (hcY i) hcY₀ h0)⟩

section Tw

variable {E : Type} [Field E] [NumberField E] [StarRing E] {W : Type} [AddCommGroup W] [Module E W] [Module (𝓞 E) W]
  [IsScalarTower (𝓞 E) E W]

theorem smul_mem_twO_of (M M₀ : Submodule (𝓞 E) W) (c : ℕ) (e : HeightOneSpectrum (𝓞 E) → ℤ) (g : 𝓞 E)
    (hg : ∀ x ∈ M, g • x ∈ M₀) {x : W} (hx : x ∈ Formalism.L2.Ker.twist₂ M c e) : g • x ∈ Formalism.L2.Ker.twist₂ M₀ c e := by
  rw [Formalism.L2.Ker.mem_twO] at hx ⊢
  intro Q
  obtain ⟨s, hs, hsx⟩ := hx Q
  refine ⟨s, hs, ?_⟩
  rw [smul_comm _ g, smul_comm s g]
  exact hg _ hsx

theorem natsmul_mem_twO (L : Submodule (𝓞 E) W) (c : ℕ) (e e' : HeightOneSpectrum (𝓞 E) → ℤ) (he : ∀ Q, e' Q ≤ e Q + 1)
    {x : W} (hx : x ∈ Formalism.L2.Ker.twist₂ L c e) : (c : 𝓞 E) • x ∈ Formalism.L2.Ker.twist₂ L c e' := by
  rcases Nat.eq_zero_or_pos c with rfl | hc
  · rw [Nat.cast_zero, zero_smul]; exact Submodule.zero_mem _
  have hcE : (c : E) ≠ 0 := by exact_mod_cast hc.ne'
  rw [Formalism.L2.Ker.mem_twO] at hx ⊢
  intro Q
  obtain ⟨n, hn⟩ : ∃ n : ℕ, (n : ℤ) = e Q + 1 - e' Q := ⟨(e Q + 1 - e' Q).toNat, Int.toNat_of_nonneg (by linarith [he Q])⟩
  have key : ((c : E) ^ e' Q)⁻¹ • ((c : 𝓞 E) • x) = ((c : 𝓞 E) ^ n) • (((c : E) ^ e Q)⁻¹ • x) := by
    rw [← IsScalarTower.algebraMap_smul E ((c : 𝓞 E) ^ n), ← IsScalarTower.algebraMap_smul E (c : 𝓞 E) x, smul_smul, smul_smul]
    congr 1
    simp only [map_pow, map_natCast]
    rw [← zpow_neg, ← zpow_neg, ← zpow_natCast, hn, ← zpow_add_one₀ hcE, ← zpow_add₀ hcE]
    congr 1; ring
  rw [key]
  exact Submodule.smul_mem _ _ (hx Q)

theorem mem_twO_zero (M : Submodule (𝓞 E) W) (c : ℕ) (x : W) : x ∈ Formalism.L2.Ker.twist₂ M c (fun _ => 0) ↔ x ∈ M := by
  rw [Formalism.L2.Ker.mem_twO]
  simp only [zpow_zero, inv_one, one_smul]
  exact ⟨fun h => Formalism.L2.Ker.mem_of_forall_locP M h, fun h Q => Formalism.L2.Ker.le_locP' M Q h⟩

end Tw

end GlobalTheory.CommonReps

namespace GlobalTheory.CommonReps

theorem common_reps_halves : ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (ι κ : Type) [Fintype ι] [Nonempty ι] [Fintype κ] (a b : ℕ) (emb : ι → E →+* ℂ) (δ : ℂ) (AA0 : Submodule (𝓞 E) E) (SS : Finset (HeightOneSpectrum (𝓞 E))) (cl : ℕ) (N₀ : Submodule (𝓞 E) (Formalism.L2.Col.Sp E a)) (N₀' : Submodule (𝓞 E) (Formalism.L2.Col.Sp E b)) (N : κ → Submodule (𝓞 E) (Formalism.L2.Col.Sp E a)) (N' : κ → Submodule (𝓞 E) (Formalism.L2.Col.Sp E b)) (g : 𝓞 E), δ ≠ 0 → (∃ k : 𝓞 E, g = 1 + (cl : 𝓞 E) * k) → (∀ i, (∀ x ∈ perO AA0 (N i) (N' i), g • x ∈ perO AA0 N₀ N₀') ∧ ∀ x ∈ perO AA0 N₀ N₀', g • x ∈ perO AA0 (N i) (N' i)) → relIdx (LamC emb δ AA0 N₀ N₀') (AC emb δ AA0 SS N₀ N₀' cl) ≠ 0 → relIdx (BC emb δ AA0 SS N₀ N₀' cl) (LamC emb δ AA0 N₀ N₀' ⊓ AC emb δ AA0 SS N₀ N₀' cl) ≠ 0 → relIdx (LamC emb δ AA0 N₀ N₀') (BC emb δ AA0 SS N₀ N₀' cl) ≠ 0 → ∃ SX SA SB : Finset (VV ι a b), ∀ i, IsReps (LamC emb δ AA0 (N i) (N' i)) (AC emb δ AA0 SS (N i) (N' i) cl) SX ∧ IsReps (BC emb δ AA0 SS (N i) (N' i) cl) (LamC emb δ AA0 (N i) (N' i) ⊓ AC emb δ AA0 SS (N i) (N' i) cl) SA ∧ IsReps (LamC emb δ AA0 (N i) (N' i)) (BC emb δ AA0 SS (N i) (N' i) cl) SB := by
  intro E _ _ _ ι κ _ _ _ a b emb δ AA0 SS cl N₀ N₀' N N' g hδ hk hmv h1 h2 h3
  obtain ⟨k, hk⟩ := hk
  set f : Formalism.L2.Col.HomE E a b →+ VV ι a b := embH emb δ with hfdef
  have hf : Function.Injective f := embH_inj emb hδ
  have hinf : ∀ M A : Submodule (𝓞 E) (Formalism.L2.Col.HomE E a b),
      M.toAddSubgroup.map f ⊓ A.toAddSubgroup.map f = (M ⊓ A).toAddSubgroup.map f := fun M A =>
    (AddSubgroup.map_inf_eq M.toAddSubgroup A.toAddSubgroup f hf).symm
  have hexpS : ∀ Q, expS SS Q ≤ 1 ∧ -1 ≤ expS SS Q := fun Q => by
    rcases Formalism.L2.Ker.expS_cases SS Q with h | h | h <;> rw [h] <;> norm_num

  have hcA : ∀ M : Submodule (𝓞 E) (Formalism.L2.Col.HomE E a b), ∀ y ∈ halfAO SS M cl, (cl : 𝓞 E) • y ∈ M := fun M y hy =>
    (mem_twO_zero M cl _).1 (natsmul_mem_twO M cl _ _ (fun Q => by linarith [(hexpS Q).1]) hy)
  have hcB : ∀ M : Submodule (𝓞 E) (Formalism.L2.Col.HomE E a b), ∀ y ∈ halfBO SS M cl, (cl : 𝓞 E) • y ∈ M := fun M y hy =>
    (mem_twO_zero M cl _).1 (natsmul_mem_twO M cl _ _ (fun Q => by linarith [(hexpS Q).2]) hy)
  have hcM : ∀ M : Submodule (𝓞 E) (Formalism.L2.Col.HomE E a b), ∀ y ∈ M, (cl : 𝓞 E) • y ∈ halfBO SS M cl := fun M y hy =>
    natsmul_mem_twO M cl (fun _ => 0) _ (fun Q => by linarith [(hexpS Q).1]) ((mem_twO_zero M cl y).2 hy)
  have hA : ∀ M M' : Submodule (𝓞 E) (Formalism.L2.Col.HomE E a b), (∀ x ∈ M, g • x ∈ M') → ∀ y ∈ halfAO SS M cl, g • y ∈ halfAO SS M' cl :=
    fun M M' h y hy => smul_mem_twO_of M M' cl _ g h hy
  have hB : ∀ M M' : Submodule (𝓞 E) (Formalism.L2.Col.HomE E a b), (∀ x ∈ M, g • x ∈ M') → ∀ y ∈ halfBO SS M cl, g • y ∈ halfBO SS M' cl :=
    fun M M' h y hy => smul_mem_twO_of M M' cl _ g h hy
  obtain ⟨SX, hSX⟩ := common_reps_of f hf g (cl : 𝓞 E) k hk (fun i => perO AA0 (N i) (N' i))
    (fun i => halfAO SS (perO AA0 (N i) (N' i)) cl) (perO AA0 N₀ N₀') (halfAO SS (perO AA0 N₀ N₀') cl)
    (fun i => hA _ _ (hmv i).1) (fun i => hA _ _ (hmv i).2) (fun i => (hmv i).1) (fun i => (hmv i).2)
    (fun i => hcA _) (hcA _) h1
  have h2' := h2
  simp only [LamC, AC, BC, laV] at h2'
  rw [hinf] at h2'
  obtain ⟨SA, hSA⟩ := common_reps_of f hf g (cl : 𝓞 E) k hk (fun i => halfBO SS (perO AA0 (N i) (N' i)) cl)
    (fun i => perO AA0 (N i) (N' i) ⊓ halfAO SS (perO AA0 (N i) (N' i)) cl) (halfBO SS (perO AA0 N₀ N₀') cl)
    (perO AA0 N₀ N₀' ⊓ halfAO SS (perO AA0 N₀ N₀') cl)
    (fun i y hy => ⟨(hmv i).1 _ hy.1, hA _ _ (hmv i).1 _ hy.2⟩) (fun i y hy => ⟨(hmv i).2 _ hy.1, hA _ _ (hmv i).2 _ hy.2⟩)
    (fun i => hB _ _ (hmv i).1) (fun i => hB _ _ (hmv i).2)
    (fun i y hy => hcM _ y hy.1) (fun y hy => hcM _ y hy.1) h2'
  obtain ⟨SB, hSB⟩ := common_reps_of f hf g (cl : 𝓞 E) k hk (fun i => perO AA0 (N i) (N' i))
    (fun i => halfBO SS (perO AA0 (N i) (N' i)) cl) (perO AA0 N₀ N₀') (halfBO SS (perO AA0 N₀ N₀') cl)
    (fun i => hB _ _ (hmv i).1) (fun i => hB _ _ (hmv i).2) (fun i => (hmv i).1) (fun i => (hmv i).2)
    (fun i => hcB _) (hcB _) h3
  refine ⟨SX, SA, SB, fun i => ⟨hSX i, ?_, hSB i⟩⟩
  have e : LamC emb δ AA0 (N i) (N' i) ⊓ AC emb δ AA0 SS (N i) (N' i) cl =
      (perO AA0 (N i) (N' i) ⊓ halfAO SS (perO AA0 (N i) (N' i)) cl).toAddSubgroup.map f := hinf _ _
  rw [e]
  exact hSA i

end GlobalTheory.CommonReps
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsCommonScaleLatticePairsSplitPrime
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F GlobalTheory.TwU TensorProduct
open Formalism.L2.Th1.H Formalism.L2.KerInert.RepComb

noncomputable section

namespace GlobalTheory.CommonScale

theorem conj_star (D : D7) (x : D.host.E) : (letI := D.host.cmStar; star x) = D.host.conj x := by
  apply D.host.φ₀.injective
  have := D.host.isCMField_hostE
  exact (IsCMField.complexEmbedding_complexConj _ D.host.φ₀ x).trans
    (D.host.conjE_apply D.host.φ₀ x).symm

theorem coprime_of_ne {R : Type} [CommRing R] {P Q : Ideal R} (hP : P.IsMaximal) (hQ : Q.IsMaximal)
    (h : P ≠ Q) : IsCoprime P Q := by
  rw [Ideal.isCoprime_iff_sup_eq]
  exact Ideal.IsMaximal.coprime_of_ne hP hQ h

theorem coprime_span {R : Type} [CommRing R] {P : Ideal R} (hP : P.IsMaximal) {c : R} (hc : c ∉ P) :
    IsCoprime P (Ideal.span {c}) := by
  rw [Ideal.isCoprime_iff_sup_eq]
  by_contra H
  have h1 : P ⊔ Ideal.span {c} = P := (hP.eq_of_le H le_sup_left).symm
  exact hc (h1 ▸ Ideal.mem_sup_right (Ideal.mem_span_singleton_self c))

theorem exists_split_one {R : Type} [CommRing R] {κ : Type} (P : Ideal R) (hP : P.IsMaximal) (c : R) (hc : c ∉ P)
    (S : Finset κ) (f g : κ → Ideal R) (hf : ∀ q ∈ S, (f q).IsMaximal ∧ P ≠ f q)
    (hg : ∀ q ∈ S, (g q).IsMaximal ∧ P ≠ g q) (M : ℕ) :
    ∃ x ∈ P ^ M, ∃ j : R, x + j = 1 ∧ j ∈ Ideal.span {c} ∧ (∀ q ∈ S, j ∈ f q) ∧ (∀ q ∈ S, j ∈ g q) := by
  have hcop : IsCoprime (P ^ M) (Ideal.span {c} * (∏ q ∈ S, f q) * ∏ q ∈ S, g q) := by
    apply IsCoprime.pow_left
    refine IsCoprime.mul_right (IsCoprime.mul_right (coprime_span hP hc) ?_) ?_
    · exact IsCoprime.prod_right fun q hq => coprime_of_ne hP (hf q hq).1 (hf q hq).2
    · exact IsCoprime.prod_right fun q hq => coprime_of_ne hP (hg q hq).1 (hg q hq).2
  rw [Ideal.isCoprime_iff_sup_eq] at hcop
  have h1 : (1 : R) ∈ P ^ M ⊔ (Ideal.span {c} * (∏ q ∈ S, f q) * ∏ q ∈ S, g q) := by
    rw [hcop]; exact Submodule.mem_top
  obtain ⟨x, hx, j, hj, hxj⟩ := Submodule.mem_sup.1 h1
  refine ⟨x, hx, j, hxj, Ideal.mul_le_left (Ideal.mul_le_left hj), fun q hq => ?_, fun q hq => ?_⟩
  · exact (Ideal.prod_le_inf.trans (Finset.inf_le (f := f) hq)) (Ideal.mul_le_right (Ideal.mul_le_left hj))
  · exact (Ideal.prod_le_inf.trans (Finset.inf_le (f := g) hq)) (Ideal.mul_le_right hj)

theorem scale : letI := fun D : D7 => D.host.cmStar; ∀ (D : D7) (P : HeightOneSpectrum (𝓞 D.host.E)) (SS : Finset (HeightOneSpectrum (𝓞 D.host.E))) (cl : ℕ), P ∉ SS → Formalism.L2.Col.conjPrime₂ P ∉ SS → ((cl : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal → ∀ (ι : Type) [Fintype ι] (a b : ℕ) (N : ι → Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (N₀ : Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (N' : ι → Submodule (𝓞 D.host.E) (Fin b → D.host.E)) (N₀' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)), (∀ i, GL3Theta.EqOff D P (N i) N₀ ∧ GL3Theta.EqOff D P (N' i) N₀') → ∃ g : 𝓞 D.host.E, (∃ k : 𝓞 D.host.E, g = 1 + (cl : 𝓞 D.host.E) * k) ∧ (∀ Q ∈ SS, g ∉ Q.asIdeal) ∧ ∀ i, ((∀ x ∈ N i, g • x ∈ N₀) ∧ ∀ x ∈ N₀, g • x ∈ N i) ∧ ((∀ x ∈ N' i, g • x ∈ N₀') ∧ ∀ x ∈ N₀', g • x ∈ N' i) := by
  intro D P SS cl hP hPc hcl ι _ na nb N N₀ N' N₀' h
  choose m₁ hm₁ using fun i => (h i).1
  choose m₂ hm₂ using fun i => (h i).2
  have hle₁ : ∀ i, m₁ i ≤ ∑ i, (m₁ i + m₂ i) := fun i =>
    le_trans (Nat.le_add_right _ _) (Finset.single_le_sum (f := fun i => m₁ i + m₂ i) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i))
  have hle₂ : ∀ i, m₂ i ≤ ∑ i, (m₁ i + m₂ i) := fun i =>
    le_trans (Nat.le_add_left _ _) (Finset.single_le_sum (f := fun i => m₁ i + m₂ i) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i))
  have cc : ∀ Q : HeightOneSpectrum (𝓞 D.host.E), Formalism.L2.Col.conjPrime₂ (Formalism.L2.Col.conjPrime₂ Q) = Q := by
    intro Q
    apply HeightOneSpectrum.ext
    ext r
    rw [Formalism.L2.Col.mem_conjP, Formalism.L2.Col.mem_conjP, Formalism.L2.Col.cO_cO]
  obtain ⟨x, hx, j, hxj, hjcl, hjQ, hjQ'⟩ := exists_split_one P.asIdeal P.isMaximal _ hcl SS
    (fun Q => Q.asIdeal) (fun Q => (Formalism.L2.Col.conjPrime₂ Q).asIdeal)
    (fun Q hQ => ⟨Q.isMaximal, fun e => hP (HeightOneSpectrum.ext e ▸ hQ)⟩)
    (fun Q hQ => ⟨(Formalism.L2.Col.conjPrime₂ Q).isMaximal, fun e => hPc (by rw [HeightOneSpectrum.ext e, cc]; exact hQ)⟩)
    (∑ i, (m₁ i + m₂ i))
  have hxQ : ∀ Q : HeightOneSpectrum (𝓞 D.host.E), j ∈ Q.asIdeal → x ∉ Q.asIdeal := fun Q hj' hx' =>
    Q.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 (by rw [← hxj]; exact Q.asIdeal.add_mem hx' hj'))
  have hy : ((Formalism.L2.Col.cO D.host.E x : 𝓞 D.host.E) : D.host.E) = D.host.conj (x : D.host.E) :=
    conj_star D (x : D.host.E)
  refine ⟨x * Formalism.L2.Col.cO D.host.E x, ?_, ?_, ?_⟩
  · obtain ⟨t, ht⟩ := Ideal.mem_span_singleton.1 hjcl
    have hx1 : x = 1 - (cl : 𝓞 D.host.E) * t := by rw [← ht, ← hxj]; ring
    refine ⟨-t - Formalism.L2.Col.cO D.host.E t + (cl : 𝓞 D.host.E) * t * Formalism.L2.Col.cO D.host.E t, ?_⟩
    rw [hx1, map_sub, map_one, map_mul, map_natCast]; ring
  · intro Q hQ hg
    rcases Q.isPrime.mem_or_mem hg with h1 | h1
    · exact hxQ Q (hjQ Q hQ) h1
    · exact hxQ (Formalism.L2.Col.conjPrime₂ Q) (hjQ' Q hQ) ((Formalism.L2.Col.mem_conjP Q x).2 h1)
  · intro i
    exact ⟨hm₁ i x _ hy (Ideal.pow_le_pow_right (hle₁ i) hx), hm₂ i x _ hy (Ideal.pow_le_pow_right (hle₂ i) hx)⟩

end GlobalTheory.CommonScale
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.HostFieldPadicEmbeddingMemMaxUnramified
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Formalism.MainNotions.N
open scoped Pointwise

namespace GlobalTheory.HostKur

theorem host_image_mem_Kur : ∀ {R : Ranks} (H : Host R) (l : ℕ) [Fact l.Prime], l ∉ H.small → l ≠ H.q → l ≠ H.d →
    ∀ (c : H.E →+* PadicAlgCl l) (x : H.E), c x ∈ Loc.MaximalUnramifiedExtension l := by
  intro R H l _ hl2 hq hd c x
  exact GlobalTheory.HubLoc.image_mem_Kur H c (UpperTheory.Small.not_dvd_condN H Fact.out hl2 hq hd) x

end GlobalTheory.HostKur
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.InertHeckeOperatorsRowsRationalSelfAdjointLabels
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.InertRows

theorem ext_right_inv {G Γ W K : Type} [Group G] [Group Γ] [NormedAddCommGroup W] [InnerProductSpace ℂ W] [Field K]
    [NumberField K] [StarRing K] (ι : Γ →* G) (S : CSD K) (σ : K →+* ℂ) (ρ : Γ →* Module.End ℂ W) (J : Subgroup G)
    (χ : J →* ℂˣ) (P : Bridge.ClassPres ι S σ ρ J χ) (f : S.Forms) (g : G) (k : J) (hk : χ k = 1) :
    P.ext f (g * k) = P.ext f g := by
  have := (GlobalTheory.classPres_basic ι S σ ρ J χ P).1 f 1 g k
  rwa [hk, map_one, map_one, one_mul, Module.End.one_apply, Units.val_one, one_smul] at this

theorem ext_op_eq {D : D7} (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E))
    (L : LevDat D.host.E ℂ V.rank) (hβ : IsSDFrame V β Λ 1) {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    (ρ : GQ V →* Module.End ℂ W) {K : Type} [Field K] [NumberField K] [StarRing K] (σ : K →+* ℂ) (S : CSD K)
    (Pr : Bridge.ClassPres (Bridge.ratF V) S σ ρ (levEnv V β L).J (levEnv V β L).χ)
    {I : Type} (pl : I → Pl D.host.E) (ty : I → List ℤ) (op : I → Module.End K S.Forms) (inR : I → Prop)
    (HT : Bridge.HeckeTie (Bridge.ratF V) Pr op inR (fun i => IsLabElt V (pl i) (ty i)) (fun i => IsLocElt V (pl i)))
    (i : I) (hi : inR i) (hgood : ∀ PP, PP ∈ L.Pg ∨ PP ∈ L.Q → PP ≠ pl i ∧ ¬ Formalism.IndefR.Lev.IsConjPl PP (pl i))
    (hpw : (ty i).Pairwise (fun a b => b ≤ a)) :
    IsLab V (pl i) (ty i) ∧ ∀ f : S.Forms, Pr.extL (op i f) = hkF V (pl i) (Finsupp.single (ty i) 1) (Pr.extL f) := by
  refine hβ.elim fun c hc => ?_
  have hc' : IsBaseFrame V β Λ 1 := (one_pow c : (1 : ℕ) ^ c = 1) ▸ hc
  have h1 : ((1 : ℕ) : 𝓞 D.host.E) ∉ (pl i).asIdeal := by
    rw [Nat.cast_one]; exact (Ideal.ne_top_iff_one _).1 (pl i).isPrime.ne_top
  have hd := _root_.GlobalTheory.HkDict.dcOp_eq_label V β Λ 1 L hc' (pl i) h1 hgood (ty i) (HT.hx i) (HT.hA i) hpw
    (HT.hx_ok i hi) (HT.hA_loc i hi) (HT.hDC i hi)
  exact ⟨hd.1, fun f => (HT.op_eq i hi f).trans (hd.2 W (Pr.ext f) fun g k hk =>
    ext_right_inv _ S σ ρ _ _ Pr f g k (HT.chi_loc i hi k hk))⟩

theorem csum_selfAdj {G Γ W K : Type} [Group G] [Group Γ] [NormedAddCommGroup W] [InnerProductSpace ℂ W] [Field K]
    [NumberField K] [StarRing K] (ι : Γ →* G) (S : CSD K) (σ : K →+* ℂ) (ρ : Γ →* Module.End ℂ W) (J : Subgroup G)
    (χ : J →* ℂˣ) (P : Bridge.ClassPres ι S σ ρ J χ) (M : HMod (G → W))
    (hM : M.Is (Bridge.AdForms ι ρ J χ) (Bridge.adInner ι J P.y)) (j : S.Forms → M.H) (hj : ∀ x, M.e (j x) = P.extL x)
    (U : Module.End K S.Forms) (u : Module.End ℂ M.H) (hu : LinearMap.adjoint u = u) (hU : ∀ f, j (U f) = u (j f))
    (f g : S.Forms) :
    S.csum ((U f : S.Forms) : S.Cl → S.V) (g : S.Cl → S.V) = S.csum (f : S.Cl → S.V) ((U g : S.Forms) : S.Cl → S.V) := by
  have hs : ∀ f g : S.Forms, inner ℂ (j f) (j g) = σ (S.csum (f : S.Cl → S.V) (g : S.Cl → S.V)) := by
    intro f g
    rw [hM.2.2, hj, hj]
    exact (GlobalTheory.classPres_basic ι S σ ρ J χ P).2.1 f g
  apply σ.injective
  rw [← hs, ← hs, hU, hU, ← LinearMap.adjoint_inner_right, hu]

theorem dualC_single {d : List ℤ} (h : dualLab d = d) :
    dualC (Finsupp.mapRange star (star_zero ℂ) (Finsupp.single d (1 : ℂ))) = Finsupp.single d 1 := by
  rw [Finsupp.mapRange_single, star_one, dualC, Finsupp.mapDomain_single, h]

theorem inert_rows : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), R.toLevCh.Is A.μ0 → R.IsFam → R.IsModels → ∀ t, ∀ (I : Type) (pl : I → Pl D.host.E) (ty : I → List ℤ) (op : I → Module.End D.what₂.LL (A.MtildeCSD t).Forms) (inR : I → Prop), (∀ i, inR i → Good R t (pl i) ∧ conjPl (pl i) = pl i ∧ (ty i).Pairwise (fun a b => b ≤ a)) → Bridge.HeckeTie (Bridge.ratF D.sp.X') (R.B.R t).pres op inR (fun i => IsLabElt D.sp.X' (pl i) (ty i)) (fun i => IsLocElt D.sp.X' (pl i)) → ∀ i, inR i → (∀ a b, LinearMap.toMatrix (A.MtildeCSD t).basis (A.MtildeCSD t).basis (op i) a b ∈ cmMax D.what₂.LL) ∧ (∀ f g : (A.MtildeCSD t).Forms, (A.MtildeCSD t).csum ((op i f : (A.MtildeCSD t).Forms) : (A.MtildeCSD t).Cl → (A.MtildeCSD t).V) (g : (A.MtildeCSD t).Cl → (A.MtildeCSD t).V) = (A.MtildeCSD t).csum (f : (A.MtildeCSD t).Cl → (A.MtildeCSD t).V) ((op i g : (A.MtildeCSD t).Forms) : (A.MtildeCSD t).Cl → (A.MtildeCSD t).V)) ∧ IsLab D.sp.X' (pl i) (ty i) ∧ ∀ h, IsOpsX R t h → ∀ f, R.jX t (op i f) = h (pl i) (Finsupp.single (ty i) 1) (R.jX t f) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hL hF hM t I pl ty op inR hin HT i hi
  have hgood := (hin i hi).1
  have hconj := (hin i hi).2.1
  have hpw := (hin i hi).2.2
  have hd := ext_op_eq D.sp.X' R.βX R.ΛX (R.datXt t) hL.βX R.cX.coef.ρ D.what₂.embLL (A.MtildeCSD t) (R.B.R t).pres
    pl ty op inR HT i hi hgood hpw
  have hint : ∀ h, IsOpsX R t h → ∀ f, R.jX t (op i f) = h (pl i) (Finsupp.single (ty i) 1) (R.jX t f) := by
    intro h hh f
    refine (hM.HX t).1 ?_
    refine (hM.jX t _).trans (Eq.trans ?_ (hh (pl i) hgood _ _).symm)
    exact (hd.2 f).trans (congrArg (hkF D.sp.X' (pl i) (Finsupp.single (ty i) 1)) (hM.jX t f).symm)
  refine ⟨fun a b => GlobalTheory.HeckeRational.rows_dcOp_mem_cmMax R hF.tie t _ _ (HT.op_eq i hi) a b, fun f g => ?_, hd.1, hint⟩
  refine ((GlobalTheory.T.realization_family_normal_operators R F hL hF hM).1 t).elim fun h hh => ?_
  have hdual : dualLab (ty i) = ty i := ((_root_.GlobalTheory.LabChar.labels_char D.sp.X' (pl i) (ty i)).1 hd.1).2.2 hconj
  have hadj := (hh.2.2 (pl i) hgood (Finsupp.single (ty i) 1)).trans (congrArg (h (pl i)) (dualC_single hdual))
  exact csum_selfAdj (Bridge.ratF D.sp.X') (A.MtildeCSD t) D.what₂.embLL R.cX.coef.ρ _ _ (R.B.R t).pres (R.HX t) (hM.HX t)
    (R.jX t) (hM.jX t) (op i) _ hadj (hint h hh.1) f g

end GlobalTheory.InertRows
end

