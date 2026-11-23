module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0020
public import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsProjectiveOverRingByChartsAbelianVariety
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1432
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0718
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0765
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ExistsPowPrincipalFractionalIdeal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1412
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0753
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0751
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0620
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1422
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1438
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0045
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0007
public import Formalism.LocalToGlobal.ProjectiveLattices.SpMapAlgHomId
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0060
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsLevMoveOfFrOver
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0111
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0110
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0055
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0140
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LevelMapFibreSimplyTransitive
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1430

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormChartLineBundleBaseChangeFieldExtension
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ProjField
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.ProjField

open GlobalTheory.AbelianProjective

section BaseChange

variable {S S' : Scheme.{0}} (f : S' ⟶ S)

abbrev bcProj (X : Over S) : ((Over.pullback f).obj X).left ⟶ X.left := pullback.fst X.hom f

theorem map_left_bcProj {X Y : Over S} (g : X ⟶ Y) :
    ((Over.pullback f).map g).left ≫ bcProj f Y = bcProj f X ≫ g.left := by
  simp only [Over.pullback_map_left]
  exact pullback.lift_fst _ _ _

theorem isPullback_bcProj {X Y : Over S} (g : X ⟶ Y) :
    IsPullback (bcProj f X) ((Over.pullback f).map g).left g.left (bcProj f Y) := by
  refine IsPullback.of_bot (v₂₁ := pullback.snd Y.hom f) (v₂₂ := Y.hom) (h₃₁ := f) ?_ (map_left_bcProj f g).symm
    (IsPullback.of_hasPullback Y.hom f)
  have e : ((Over.pullback f).map g).left ≫ pullback.snd Y.hom f = pullback.snd X.hom f := by
    simp only [Over.pullback_map_left]
    exact pullback.lift_snd _ _ _
  rw [e, Over.w]
  exact IsPullback.of_hasPullback X.hom f

def bcProd (X Y : Over S) : ((Over.pullback f).obj X ⊗ (Over.pullback f).obj Y).left ⟶ (X ⊗ Y).left :=
  (Functor.LaxMonoidal.μ (Over.pullback f) X Y).left ≫ bcProj f (X ⊗ Y)

theorem bcProd_fst (X Y : Over S) :
    bcProd f X Y ≫ (fst X Y).left = (fst ((Over.pullback f).obj X) ((Over.pullback f).obj Y)).left ≫ bcProj f X := by
  rw [bcProd, Category.assoc, ← map_left_bcProj, ← Category.assoc, ← Over.comp_left, Functor.Monoidal.μ_fst]

theorem bcProd_snd (X Y : Over S) :
    bcProd f X Y ≫ (snd X Y).left = (snd ((Over.pullback f).obj X) ((Over.pullback f).obj Y)).left ≫ bcProj f Y := by
  rw [bcProd, Category.assoc, ← map_left_bcProj, ← Category.assoc, ← Over.comp_left, Functor.Monoidal.μ_snd]

theorem bcProd_whiskerRight {W V : Over S} (π : W ⟶ V) (X : Over S) :
    ((Over.pullback f).map π ▷ (Over.pullback f).obj X).left ≫ bcProd f V X = bcProd f W X ≫ (π ▷ X).left := by
  rw [bcProd, bcProd, ← Category.assoc, ← Over.comp_left, Functor.LaxMonoidal.μ_natural_left, Over.comp_left,
    Category.assoc, map_left_bcProj, Category.assoc]

end BaseChange

section Group

variable {S S' : Scheme.{0}} (f : S' ⟶ S)

theorem bcSum_eq {W X : Over S} [GrpObj X] (a : W ⟶ X) :
    (fst ((Over.pullback f).obj W) ((Over.pullback f).obj X) ≫ (Over.pullback f).map a) *
        snd ((Over.pullback f).obj W) ((Over.pullback f).obj X) =
      Functor.LaxMonoidal.μ (Over.pullback f) W X ≫ (Over.pullback f).map ((fst W X ≫ a) * snd W X) := by
  rw [Hom.mul_def, Hom.mul_def, Functor.map_comp, Functor.obj.μ_def, ← Functor.Monoidal.lift_μ]
  simp only [← Category.assoc]
  congr 2
  rw [comp_lift, Functor.map_comp, Functor.Monoidal.μ_fst_assoc, Functor.Monoidal.μ_snd]

theorem bcSum_left {W X : Over S} [GrpObj X] (a : W ⟶ X) :
    ((fst ((Over.pullback f).obj W) ((Over.pullback f).obj X) ≫ (Over.pullback f).map a) *
        snd ((Over.pullback f).obj W) ((Over.pullback f).obj X)).left ≫ bcProj f X =
      bcProd f W X ≫ ((fst W X ≫ a) * snd W X).left := by
  rw [bcSum_eq, Over.comp_left, Category.assoc, map_left_bcProj, bcProd, Category.assoc]

end Group

theorem surjective_spMap (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] : Surjective (spMap (algebraMap K Ω)) := by
  refine ⟨fun x => ?_⟩
  have : Subsingleton (Sp K) := inferInstanceAs (Subsingleton (PrimeSpectrum K))
  have : Nonempty (Sp Ω) := inferInstanceAs (Nonempty (PrimeSpectrum Ω))
  exact ⟨Classical.arbitrary _, Subsingleton.elim _ _⟩

theorem normChart_baseChange : ∀ (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] (A : Over (Sp K)) [GrpObj A],
    IsAbelianScheme A → ∀ N₀ : LB A.left, N₀.IsLB → NormChart A N₀ →
      NormChart ((Over.pullback (spMap (algebraMap K Ω))).obj A)
        (N₀.pull (pullback.fst A.hom (spMap (algebraMap K Ω)))) := by
  intro K Ω _ _ _ A _ _ N₀ hN₀ ⟨W, V, π, a, U, N, n, hπ, ha, hW, hWt, hU, hUne, hN, H, hloc⟩
  have hf := surjective_spMap K Ω
  set f := spMap (algebraMap K Ω)
  have hsurj : ∀ X : Over (Sp K), Function.Surjective (bcProj f X) := fun X =>
    (MorphismProperty.of_isPullback (P := @Surjective) (IsPullback.of_hasPullback X.hom f).flip hf).surj
  have sq := bcProd_whiskerRight f π A
  have pb : IsPullback (bcProd f W A) ((Over.pullback f).map π ▷ (Over.pullback f).obj A).left (π ▷ A).left
      (bcProd f V A) := by
    refine IsPullback.of_right (h₁₂ := (fst W A).left) (v₁₃ := π.left) (h₂₂ := (fst V A).left) ?_ sq.symm
      (isPullback_whiskerRight π A)
    rw [bcProd_fst, bcProd_fst]
    exact (isPullback_whiskerRight _ _).paste_horiz (isPullback_bcProj f π)
  refine ⟨(Over.pullback f).obj W, (Over.pullback f).obj V, (Over.pullback f).map π, (Over.pullback f).map a,
    bcProj f A ⁻¹ᵁ U, N.pull (bcProd f V A), GlobalTheory.Cartier.secPull n (bcProd f V A),
    MorphismProperty.of_isPullback (isPullback_bcProj f π) hπ,
    MorphismProperty.of_isPullback (isPullback_bcProj f a) ha, ?_, ?_, ?_, ?_, LB.isLB_pull hN _, ?_, ?_⟩
  · obtain ⟨w⟩ := hW
    obtain ⟨w', -⟩ := hsurj W w
    exact ⟨w'⟩
  · exact MorphismProperty.of_isPullback (P := @LocallyOfFiniteType) (IsPullback.of_hasPullback W.hom f) hWt
  · have : IsAffineHom (bcProj f A) :=
      MorphismProperty.of_isPullback (P := @IsAffineHom) (IsPullback.of_hasPullback A.hom f).flip inferInstance
    exact hU.preimage _
  · obtain ⟨u, hu⟩ := hUne
    obtain ⟨u', rfl⟩ := hsurj A u
    exact ⟨u', hu⟩
  · let r := bcProd f V A
    let b := (snd V A).left
    let d := bcProj f A
    let c := (snd ((Over.pullback f).obj V) ((Over.pullback f).obj A)).left
    change LBIso (N.pull r) ((N₀.pull d).pull c)
    refine LBIso.trans (LB.isLB_pull hN r) (LB.isLB_pull (LB.isLB_pull hN₀ b) r)
      (LB.isLB_pull (LB.isLB_pull hN₀ d) c) ?_ ?_
    · obtain ⟨w, hw⟩ := H
      exact ⟨GlobalTheory.lbIsoPull w r, ReciprocityTheory.ChartRestriction.G.DVR.linCombIso_isGen w hw _ _⟩
    · exact GlobalTheory.FiniteAmple.lbIso_pull_pull b hN₀ (bcProd_snd f V A)
  · intro x'
    rw [GlobalTheory.Cartier.nonzeroLocus_secPull]
    change bcProd f V A x' ∈ Out.nonzeroLocus n ↔ _
    rw [hloc]
    constructor
    · intro h z' hz'
      change bcProj f A (((fst _ _ ≫ (Over.pullback f).map a) * snd _ _).left z') ∈ U
      rw [← Scheme.Hom.comp_apply, bcSum_left, Scheme.Hom.comp_apply]
      refine h _ ?_
      rw [← Scheme.Hom.comp_apply, ← sq, Scheme.Hom.comp_apply, hz']
    · intro h z hz
      obtain ⟨z', rfl, hz'⟩ := Scheme.exists_preimage_of_isPullback pb z x' hz
      have h' := h z' hz'
      change bcProj f A (((fst _ _ ≫ (Over.pullback f).map a) * snd _ _).left z') ∈ U at h'
      rw [← Scheme.Hom.comp_apply, bcSum_left, Scheme.Hom.comp_apply] at h'
      exact h'

end GlobalTheory.ProjField
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalisedFamilyEqTensorPowerVacuum
section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker

noncomputable section

namespace GlobalTheory.FamilyTieProof

theorem std : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ), TaylorLogMetric.adm1 D → GL3Theta.InducedCMType D → TaylorLogMetric.IsCurveIdeal D cc → TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ → B.kc.YFinite → ∀ N N' : ℕ, Even N → Even N' → StandardLatticesGL3.ThetaVectorUpToUnits D (TaylorLogMetric.tor0 D cc δ) (B.ω₀ / 2) (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N') (B.thZero N N') := _root_.GlobalTheory.BaseVacuum.thetaVectorUpToUnits_thZero_of_even

theorem detn1 : ∀ (D : D7) (N : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)), StandardLatticesGL3.SD D L → TaylorLogMetric.N1 D (TaylorLogMetric.detId D (StandardLatticesGL3.stdL D N) L) := _root_.GlobalTheory.SelfDualDetNorm.detId_normOne

theorem chin1 : ∀ (D : D7) (χ : TaylorLogMetric.IdE D → ℂ), TaylorLogMetric.IsChi D χ → ∀ 𝔞 : TaylorLogMetric.IdE D, TaylorLogMetric.N1 D 𝔞 → StandardLatticesGL3.Mod1All (χ 𝔞) := _root_.GlobalTheory.CharModOne.mod1All_of_isChi

theorem mod1All_mul' {a b : ℂ} (ha : StandardLatticesGL3.Mod1All a) (hb : StandardLatticesGL3.Mod1All b) : StandardLatticesGL3.Mod1All (a * b) := by
  obtain ⟨h1, h1'⟩ := ha
  obtain ⟨h2, h2'⟩ := hb
  refine ⟨mul_mem h1 h2, fun σ => ?_⟩
  have e : (⟨a * b, mul_mem h1 h2⟩ : TaylorLogMetric.Qbar) = ⟨a, h1⟩ * ⟨b, h2⟩ := rfl
  rw [e, map_mul, norm_mul, h1' σ, h2' σ, one_mul]

theorem mod1All_inv {a : ℂ} (ha : StandardLatticesGL3.Mod1All a) : StandardLatticesGL3.Mod1All a⁻¹ := by
  obtain ⟨h1, h1'⟩ := ha
  refine ⟨inv_mem h1, fun σ => ?_⟩
  have e : (⟨a⁻¹, inv_mem h1⟩ : TaylorLogMetric.Qbar) = (⟨a, h1⟩ : TaylorLogMetric.Qbar)⁻¹ := rfl
  rw [e, map_inv₀, norm_inv, h1' σ, inv_one]

theorem mod1All_pow {a : ℂ} (ha : StandardLatticesGL3.Mod1All a) (n : ℕ) : StandardLatticesGL3.Mod1All (a ^ n) := by
  induction n with
  | zero =>
    refine ⟨by simpa using one_mem TaylorLogMetric.Qbar, fun σ => ?_⟩
    have e : (⟨a ^ 0, by simpa using one_mem TaylorLogMetric.Qbar⟩ : TaylorLogMetric.Qbar) = 1 := by ext; simp
    rw [e, map_one, norm_one]
  | succ n ih => rw [pow_succ]; exact mod1All_mul' ih ha

theorem mod1All_zpow {a : ℂ} (ha : StandardLatticesGL3.Mod1All a) (n : ℤ) : StandardLatticesGL3.Mod1All (a ^ n) := by
  cases n with
  | ofNat n => simpa using mod1All_pow ha n
  | negSucc n => rw [zpow_negSucc]; exact mod1All_inv (mod1All_pow ha _)

theorem genusOneVacuum_const_mul_modulusOne {D : D7} {T : TaylorLogMetric.Tor D} {t0 : ℂ} {N N' : ℕ} {L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)}
    {L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)} {G : TaylorLogMetric.VC D N N' → ℂ} {c : ℂ} (hc : StandardLatticesGL3.Mod1All c)
    (hG : StandardLatticesGL3.ThetaVectorUpToUnits D T t0 L L' G) : StandardLatticesGL3.ThetaVectorUpToUnits D T t0 L L' (fun z => c * G z) := by
  obtain ⟨b, κ, hb, hκ, rfl⟩ := hG
  exact ⟨b, c * κ, hb, mod1All_mul' hc hκ, funext fun z => by simp only [mul_assoc]⟩

theorem genusOneVacuum_indep_twoTorsionPoint {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (hc : StandardLatticesGL3.Crv D cc δ) {t t' : ℂ}
    (ht : GL3Theta.IsTwoTorsionPointUnkilled D (TaylorLogMetric.lamOf D cc δ) t) (ht' : GL3Theta.IsTwoTorsionPointUnkilled D (TaylorLogMetric.lamOf D cc δ) t') {N N' : ℕ}
    {L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)} {L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)}
    {G : TaylorLogMetric.VC D N N' → ℂ} (h : StandardLatticesGL3.ThetaVectorUpToUnits D (TaylorLogMetric.tor0 D cc δ) t L L' G) :
    StandardLatticesGL3.ThetaVectorUpToUnits D (TaylorLogMetric.tor0 D cc δ) t' L L' G := by
  have e : GL3Theta.th0 (TaylorLogMetric.lamOf D cc δ) t = GL3Theta.th0 (TaylorLogMetric.lamOf D cc δ) t' := by
    have := GlobalTheory.ThetaConj.evenTheta_add_lattice_mem (GlobalTheory.ThetaConj.isLat_lamOf hc) t' (GlobalTheory.Glob.isThetaZero_unique_lattice hc ht ht')
    rwa [add_sub_cancel] at this
  unfold StandardLatticesGL3.ThetaVectorUpToUnits at h ⊢
  exact e ▸ h

theorem chiFac_mod1All (D : D7) (χ : TaylorLogMetric.IdE D → ℂ) (hχ : TaylorLogMetric.IsChi D χ) (N N' : ℕ)
    (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E))
    (hA : TaylorLogMetric.admitted D N N' L L') : StandardLatticesGL3.Mod1All (Base.chiFac (D := D) χ N N' L L') :=
  mod1All_mul' (mod1All_zpow (chin1 D χ hχ _ (detn1 D N L hA.2.2.1)) _)
    (mod1All_zpow (chin1 D χ hχ _ (detn1 D N' L' hA.2.2.2)) _)

theorem familyTie : GlobalTheory.ColNorms.FamilyTie := by
  intro D cc δ B χ ha hp hcc hδ hχ hY t0 ht N N' L L' hA
  have hc : StandardLatticesGL3.Crv D cc δ := ⟨hcc, hδ⟩
  have h0 := genusOneVacuum_indep_twoTorsionPoint hc B.t0 ht (std D cc δ B ha hp hcc hδ hY N N' hA.1 hA.2.1)
  exact genusOneVacuum_const_mul_modulusOne (chiFac_mod1All D χ hχ N N' L L' hA)
    (GlobalTheory.MovedVacuum.isVacuum_movedThetaVacuum D cc δ B t0 hc ht N N' L L' hA.2.2.1 hA.2.2.2 h0)

end GlobalTheory.FamilyTieProof
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowerSeriesPowPFrobenius
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.EtLev

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.UPel.HT.PrimTors

theorem exists_finite_flat_wPow : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (w0 : Ideal (𝓞 D.F)), w0.IsMaximal → (p : 𝓞 D.F) ∈ w0 → ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (s : S ⟶ Sp R) (o : Obj b N s) (r : ℕ), ∃ r' : ℕ, r ≤ r' ∧ ∃ (H : Over S) (i : H ⟶ o.A), IsFinite H.hom ∧ Flat H.hom ∧ (∀ c ∈ w0 ^ r', i ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1) ∧ ∀ (T : Over S) (x : T ⟶ o.A), (∀ c ∈ w0 ^ r', x ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1) → ∃! y : T ⟶ H, y ≫ i = x := by
  intro p _ D R _ b N w0 _ hp S _ s o r
  have hw0 : w0 ≠ ⊥ := by
    intro h
    rw [h, Ideal.mem_bot] at hp
    exact (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero) hp
  have hwr : w0 ^ r ≠ ⊥ := by
    rw [Ne, ← Ideal.zero_eq_bot] at *
    exact pow_ne_zero r hw0
  obtain ⟨K, _, i, -, _, hfin, hflat, hK⟩ :=
    GlobalTheory.IwLevel.HTTorsionFF.exists_torsion_finite_flat p D R b N (w0 ^ r) S s o hwr
  have key : ∀ (T : Over S) (x : T ⟶ o.A),
      GlobalTheory.IwLevel.KilledBy (GlobalTheory.IwLevel.htAct o) ((w0 ^ r).map (algebraMap (𝓞 D.F) D.O)) x ↔
        ∀ c ∈ w0 ^ r, x ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1 := by
    intro T x
    unfold Ideal.map
    rw [GlobalTheory.IwLevel.killedBy_span]
    constructor
    · intro h c hc
      exact h _ ⟨c, hc, rfl⟩
    · rintro h _ ⟨c, hc, rfl⟩
      exact h c hc
  refine ⟨r, le_rfl, K, i, hfin, hflat, (key _ i).1 ((hK _ i).1 ⟨𝟙 _, Category.id_comp _⟩), fun T x hx => ?_⟩
  obtain ⟨y, hy⟩ := (hK T x).2 ((key T x).2 hx)
  exact ⟨y, hy, fun y' hy' => (cancel_mono i).1 (hy'.trans hy.symm)⟩

end GlobalTheory.UPel.HT.PrimTors
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectiveLineChartFamiliesAgreeOnOverlap
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.LineConst

noncomputable section

namespace GlobalTheory.LineConst
open Polynomial

variable {k : Type} [Field k]

private theorem scaleX_isUnit (R : Type) [CommRing R] [Algebra k R] {u v : R} (huv : u * v = 1) :
    IsUnit ((algebraMap (Polynomial R) (Localization.Away (X : Polynomial R))).comp (scaleHom k R u) X) := by
  simp only [RingHom.comp_apply, scaleHom, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X, map_mul]
  refine IsUnit.mul ?_ (IsLocalization.Away.algebraMap_isUnit _)
  exact ((isUnit_iff_exists_inv.mpr ⟨v, huv⟩).map Polynomial.C).map _

private def psiHom (R : Type) [CommRing R] [Algebra k R] {u v : R} (huv : u * v = 1) :
    Localization.Away (X : Polynomial k) →+* Localization.Away (X : Polynomial R) :=
  IsLocalization.Away.lift (X : Polynomial k) (scaleX_isUnit R huv)

private theorem psi_loc (R : Type) [CommRing R] [Algebra k R] {u v : R} (huv : u * v = 1) :
    (algebraMap (Polynomial R) (Localization.Away (X : Polynomial R))).comp (scaleHom k R u) =
      (psiHom R huv).comp (algebraMap (Polynomial k) (Localization.Away (X : Polynomial k))) :=
  RingHom.ext fun a => by simp only [RingHom.comp_apply, psiHom, IsLocalization.Away.lift_eq]

private theorem psi_inv (R : Type) [CommRing R] [Algebra k R] {u v : R} (huv : u * v = 1) :
    (Polynomial.aeval (IsLocalization.Away.invSelf (X : Polynomial R) :
        Localization.Away (X : Polynomial R))).toRingHom.comp (scaleHom k R v) =
      (psiHom R huv).comp (Polynomial.aeval (IsLocalization.Away.invSelf (X : Polynomial k) :
        Localization.Away (X : Polynomial k))).toRingHom := by
  apply Polynomial.ringHom_ext
  · intro a
    have e : (algebraMap k (Localization.Away (X : Polynomial k))) a =
        algebraMap (Polynomial k) (Localization.Away (X : Polynomial k)) (Polynomial.C a) := by
      rw [IsScalarTower.algebraMap_apply k (Polynomial k) (Localization.Away (X : Polynomial k))]
      rfl
    have e2 : (algebraMap R (Localization.Away (X : Polynomial R))) (algebraMap k R a) =
        algebraMap (Polynomial R) (Localization.Away (X : Polynomial R)) (Polynomial.C (algebraMap k R a)) := by
      rw [IsScalarTower.algebraMap_apply R (Polynomial R) (Localization.Away (X : Polynomial R))]
      rfl
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Polynomial.aeval_C, e, psiHom,
      IsLocalization.Away.lift_eq]
    simp [scaleHom, e2]
  · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Polynomial.aeval_X]
    have hb : psiHom R huv (algebraMap (Polynomial k) (Localization.Away (X : Polynomial k)) X) =
        algebraMap (Polynomial R) (Localization.Away (X : Polynomial R)) (Polynomial.C u) *
          algebraMap (Polynomial R) (Localization.Away (X : Polynomial R)) X := by
      simp [psiHom, IsLocalization.Away.lift_eq, scaleHom]
    have hc : psiHom R huv (algebraMap (Polynomial k) (Localization.Away (X : Polynomial k)) X) *
        psiHom R huv (IsLocalization.Away.invSelf (X : Polynomial k) : Localization.Away (X : Polynomial k)) = 1 := by
      rw [← map_mul, IsLocalization.Away.mul_invSelf, map_one]
    have hl : (Polynomial.aeval (IsLocalization.Away.invSelf (X : Polynomial R) :
        Localization.Away (X : Polynomial R))) (scaleHom k R v X) *
        psiHom R huv (algebraMap (Polynomial k) (Localization.Away (X : Polynomial k)) X) = 1 := by
      rw [hb]
      have hv : (Polynomial.aeval (IsLocalization.Away.invSelf (X : Polynomial R) :
          Localization.Away (X : Polynomial R))) (scaleHom k R v X) =
          algebraMap (Polynomial R) (Localization.Away (X : Polynomial R)) (Polynomial.C v) *
            IsLocalization.Away.invSelf (X : Polynomial R) := by
        simp [scaleHom, Polynomial.aeval_def, Polynomial.eval₂_mul]
        congr 1
      rw [hv]
      calc _ = algebraMap (Polynomial R) (Localization.Away (X : Polynomial R)) (Polynomial.C (v * u)) *
            (algebraMap (Polynomial R) (Localization.Away (X : Polynomial R)) X *
              IsLocalization.Away.invSelf (X : Polynomial R)) := by rw [map_mul, map_mul]; ring
        _ = 1 := by rw [IsLocalization.Away.mul_invSelf, mul_comm v u, huv, map_one, map_one, _root_.one_mul]
    exact left_inv_eq_right_inv hl hc

private theorem sp_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]

private theorem scaled_loc (B : Over (Sp k)) (f₀ f₁ : Sp (Polynomial k) ⟶ B.left)
    (h0 : f₀ ≫ B.hom = spMap (algebraMap k (Polynomial k)))
    (h1 : f₁ ≫ B.hom = spMap (algebraMap k (Polynomial k)))
    (hyp : spMap (algebraMap (Polynomial k) (Localization.Away (Polynomial.X : Polynomial k))) ≫ f₀ =
      spMap (Polynomial.aeval (IsLocalization.Away.invSelf (Polynomial.X : Polynomial k) :
        Localization.Away (Polynomial.X : Polynomial k))).toRingHom ≫ f₁)
    (R : Type) [CommRing R] [Algebra k R] {u v : R} (huv : u * v = 1) :
    spMap (algebraMap (Polynomial R) (Localization.Away (Polynomial.X : Polynomial R))) ≫ (scaled B f₀ h0 R u).left =
      spMap (Polynomial.aeval (IsLocalization.Away.invSelf (Polynomial.X : Polynomial R) :
        Localization.Away (Polynomial.X : Polynomial R))).toRingHom ≫ (scaled B f₁ h1 R v).left := by
  change _ ≫ spMap (scaleHom k R u) ≫ f₀ = _ ≫ spMap (scaleHom k R v) ≫ f₁
  rw [← Category.assoc, ← Category.assoc, sp_comp, sp_comp, psi_loc R huv, psi_inv R huv,
    ← sp_comp (algebraMap (Polynomial k) (Localization.Away (Polynomial.X : Polynomial k))) (psiHom R huv),
    Category.assoc, hyp, ← Category.assoc, sp_comp]

private def locOver (R : Type) [CommRing R] [Algebra k R] : Over (Sp k) :=
  Over.mk (spMap (algebraMap k (Localization.Away (Polynomial.X : Polynomial R))))

private def locIncl (R : Type) [CommRing R] [Algebra k R] : locOver (k := k) R ⟶ lineOver k R :=
  Over.homMk (spMap (algebraMap (Polynomial R) (Localization.Away (Polynomial.X : Polynomial R)))) (by
    change spMap (algebraMap (Polynomial R) (Localization.Away (Polynomial.X : Polynomial R))) ≫
      spMap (algebraMap k (Polynomial R)) = spMap (algebraMap k (Localization.Away (Polynomial.X : Polynomial R)))
    rw [sp_comp, ← IsScalarTower.algebraMap_eq])

private def locInv (R : Type) [CommRing R] [Algebra k R] : locOver (k := k) R ⟶ lineOver k R :=
  Over.homMk (spMap (Polynomial.aeval (IsLocalization.Away.invSelf (Polynomial.X : Polynomial R) :
      Localization.Away (Polynomial.X : Polynomial R))).toRingHom) (by
    change spMap (Polynomial.aeval (IsLocalization.Away.invSelf (Polynomial.X : Polynomial R) :
      Localization.Away (Polynomial.X : Polynomial R))).toRingHom ≫
      spMap (algebraMap k (Polynomial R)) = spMap (algebraMap k (Localization.Away (Polynomial.X : Polynomial R)))
    have e : (Polynomial.aeval (IsLocalization.Away.invSelf (Polynomial.X : Polynomial R) :
        Localization.Away (Polynomial.X : Polynomial R))).toRingHom.comp (algebraMap k (Polynomial R)) =
        algebraMap k (Localization.Away (Polynomial.X : Polynomial R)) := by
      refine RingHom.ext fun a => ?_
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Polynomial.algebraMap_apply,
        Polynomial.aeval_C]
      exact (IsScalarTower.algebraMap_apply k R (Localization.Away (Polynomial.X : Polynomial R)) a).symm
    rw [sp_comp, e])

theorem famMap_loc_eq : ∀ {k : Type} [Field k] (B : Over (Sp k)) [GrpObj B] (f₀ f₁ : Sp (Polynomial k) ⟶ B.left) (h0 : f₀ ≫ B.hom = spMap (algebraMap k (Polynomial k))) (h1 : f₁ ≫ B.hom = spMap (algebraMap k (Polynomial k))), spMap (algebraMap (Polynomial k) (Localization.Away (Polynomial.X : Polynomial k))) ≫ f₀ = spMap (Polynomial.aeval (IsLocalization.Away.invSelf (Polynomial.X : Polynomial k) : Localization.Away (Polynomial.X : Polynomial k))).toRingHom ≫ f₁ → ∀ (R : Type) [CommRing R] [Algebra k R] (u v : R), u * v = 1 → spMap (algebraMap (Polynomial R) (Localization.Away (Polynomial.X : Polynomial R))) ≫ famMap B f₀ h0 R u = spMap (Polynomial.aeval (IsLocalization.Away.invSelf (Polynomial.X : Polynomial R) : Localization.Away (Polynomial.X : Polynomial R))).toRingHom ≫ famMap B f₁ h1 R v := by
  intro k _ B _ f₀ f₁ h0 h1 hyp R _ _ u v huv
  have hs : ∀ {a b : R}, a * b = 1 → locIncl (k := k) R ≫ scaled B f₀ h0 R a = locInv R ≫ scaled B f₁ h1 R b := by
    intro a b hab
    ext1
    exact scaled_loc B f₀ f₁ h0 h1 hyp R hab
  have h := congrArg CommaMorphism.left
    (show locIncl (k := k) R ≫ (scaled B f₀ h0 R u * (scaled B f₀ h0 R 1)⁻¹) =
        locInv R ≫ (scaled B f₁ h1 R v * (scaled B f₁ h1 R 1)⁻¹) by
      rw [MonObj.comp_mul, GrpObj.comp_inv, MonObj.comp_mul, GrpObj.comp_inv, hs huv, hs (_root_.one_mul 1)])
  exact h

end GlobalTheory.LineConst
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullActLev
section
open NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.AllWt GlobalTheory.LevGeo GlobalTheory.LevPull GlobalTheory.FieldBC
open scoped ENNReal

noncomputable section

open CategoryTheory

namespace GlobalTheory.LevPullEquiv


set_option maxHeartbeats 1000000 in
theorem pull_actLev : ∀ (D : D7) (j : ℕ) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (d : DeltaDat Xo c 0), 1 ≤ Dw.p + Dw.q → d.IsLev → d.l₂.A = 1 → (∀ h : KA l ≤ KA d.l₂, d.r ≫ Xo.s = d.Xo₂.s ≫ ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (IntermediateField.inclusion h).toRingHom) → ∀ (G G₂ : Type) [Group G] [Group G₂] (lev : G → Dw.La →ₗ[𝓞 D.host.E] Dw.La) (lev₂ : G₂ → Dw.La →ₗ[𝓞 D.host.E] Dw.La), ActLev (Xo := Xo) c (fun g => (lev g, (LinearMap.id : Dw.La →ₗ[𝓞 D.host.E] Dw.La))) → ActLev (Xo := d.Xo₂) d.c₂ (fun g => (lev₂ g, (LinearMap.id : Dw.La →ₗ[𝓞 D.host.E] Dw.La))) → ∀ (g : G) (g₂ : G₂), CongMod l.Mb (lev₂ g₂) (lev g) → ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), ∀ f ∈ sec Xo c a n, ∀ f₂ ∈ sec d.Xo₂ d.c₂ a n, Pull d f f₂ → Pull d (actLev c (fun g => (lev g, (LinearMap.id : Dw.La →ₗ[𝓞 D.host.E] Dw.La))) g f) (actLev d.c₂ (fun g => (lev₂ g, (LinearMap.id : Dw.La →ₗ[𝓞 D.host.E] Dw.La))) g₂ f₂) := by
  intro D j H Dw l Xo c d hpq hlev hA2 hbase G G₂ _ _ lev lev₂ hact hact₂ g g₂ hcong a n f hf f₂ hf₂ hpull
  intro k _ _ _ _ hk y₂ y hov
  have e1 : evR Xo c (actLev c (fun g => (lev g, (LinearMap.id : Dw.La →ₗ[𝓞 D.host.E] Dw.La))) g f) y =
      evR Xo c f (mvPt _ _ g y) :=
    evalAt_actL hact (GlobalTheory.TransferCompare.evalWD_framed _ _) frMap_trans_id g hf.1 y
  have e2 : evR d.Xo₂ d.c₂ (actLev d.c₂ (fun g => (lev₂ g, (LinearMap.id : Dw.La →ₗ[𝓞 D.host.E] Dw.La))) g₂ f₂) y₂ =
      evR d.Xo₂ d.c₂ f₂ (mvPt _ _ g₂ y₂) :=
    evalAt_actL hact₂ (GlobalTheory.TransferCompare.evalWD_framed _ _) frMap_trans_id g₂ hf₂.1 y₂
  rw [e1, e2]
  obtain ⟨ρ, ν, hi, hmv, hfm⟩ := mvPt_spec hact.total g y
  obtain ⟨ρ₂, ν₂, hi₂, hmv₂, hfm₂⟩ := mvPt_spec hact₂.total g₂ y₂
  obtain ⟨hd, hM, -, -, -, hE, hlift, -, -⟩ := id hlev
  obtain ⟨r', m', hsq₁, hsq₂, hE'⟩ := GlobalTheory.exists_conj_levelMap D.host.E H Dw l Xo c 0 d hE ρ ν (asIso ρ₂) ν₂
    (lev g) LinearMap.id (lev₂ g₂) LinearMap.id hmv hmv₂ hcong (fun x => ⟨0, by simp⟩)
  have hov' := GlobalTheory.frOver_of_square_of_frMove D.host.E H Dw l Xo c 0 d ρ ν ρ₂ ν₂ r' m' hsq₁ hsq₂ k y _ y₂ _ hov hfm hfm₂
  obtain ⟨z₂, hz₂⟩ := hlift k hk _
  have hL : ReciprocityTheory.ChartRestriction.G.Out.Laws := _root_.GlobalTheory.abelianSchemeLaws_all.1
  have hN := GlobalTheory.levelMaps_closed hL D.host.E H Dw hpq
  obtain ⟨g', ρ', ν', hg', -, hmv', hfm'⟩ :=
    GlobalTheory.exists_levMove_of_frOver hL D.host.E H Dw l Xo c 0 d hN hd hM hE r' m' hE' k hk _ z₂ _ hz₂ hov'
  obtain ⟨e₁, e₂⟩ := GlobalTheory.levMove_comm_levelMap_of_trivial_mod D.host.E H Dw l Xo c 0 d hpq hlev hA2 hbase ρ'.hom ν'
    (g'.f d.l₂.M) (g'.f d.l₂.A) inferInstance hmv' (fun x => GlobalTheory.LevelFibre.sub_mem_of_inGam hd hg' x)
  obtain ⟨⟨ι, hι, hone⟩, -, -⟩ := GlobalTheory.T.framedPointMove_calculus D.host.E H Dw l Xo c
  have hfin := GlobalTheory.frOver_of_square_of_frMove D.host.E H Dw l Xo c 0 d (𝟙 _) ι ρ'.hom ν' d.r d.m
    (by rw [e₁, Category.comp_id]) (by rw [e₂, hι, Category.comp_id]) k _ _ z₂ _ hz₂ (hone k _) hfm'
  exact hpull k hk _ _ hfin

end GlobalTheory.LevPullEquiv
end
end

