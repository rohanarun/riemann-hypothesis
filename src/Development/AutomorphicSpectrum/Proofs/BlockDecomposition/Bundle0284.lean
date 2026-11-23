module

public import Mathlib
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.Bundle0004
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.ValuationOfValuationModSquare
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0239
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousFunctionsPeriodRingSeparation
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0275
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0231
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.FrobeniusFactorisation.PullT
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0048
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.FormUniq
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.NLeA
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ChartGrConst
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0496

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AcrToContInjective
section
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

open CategoryTheory AlgebraicGeometry DividedPowers GroundTheory.PAdicHodge GlobalTheory.LogCris GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.PAlg CrystallineSemistableComparison.B

noncomputable section

namespace GlobalTheory.CompanionTheory.ContLine

variable {l : ℕ} [Fact l.Prime]

theorem toCont_ev (A : PAlg l) (z : ℤ_[l]) : A.toCont ℤ_[l] ≫ A.evCont z = 𝟙 A :=
  Hom.ext (RingHom.ext fun _ => rfl)

theorem shift_ev (A : PAlg l) (z : ℤ_[l]) : contShift A ≫ A.evCont z = A.evCont (z + 1) :=
  Hom.ext (RingHom.ext fun _ => rfl)

theorem toCont_shift (A : PAlg l) : A.toCont ℤ_[l] ≫ contShift A = A.toCont ℤ_[l] :=
  Hom.ext (RingHom.ext fun _ => rfl)

theorem toCont_contMap {A B : PAlg l} (φ : A ⟶ B) :
    A.toCont ℤ_[l] ≫ contMap φ ℤ_[l] = φ ≫ B.toCont ℤ_[l] :=
  Hom.ext (RingHom.ext fun _ => rfl)

theorem contMap_id (A : PAlg l) : contMap (𝟙 A) ℤ_[l] = 𝟙 (A.cont ℤ_[l]) :=
  Hom.ext (RingHom.ext fun _ => rfl)

theorem contMap_comp {A B C : PAlg l} (φ : A ⟶ B) (ψ : B ⟶ C) :
    contMap (φ ≫ ψ) ℤ_[l] = contMap φ ℤ_[l] ≫ contMap ψ ℤ_[l] :=
  Hom.ext (RingHom.ext fun _ => rfl)

theorem contMap_shift {A B : PAlg l} (φ : A ⟶ B) :
    contMap φ ℤ_[l] ≫ contShift B = contShift A ≫ contMap φ ℤ_[l] :=
  Hom.ext (RingHom.ext fun _ => rfl)

def Xi (P : PAlg l ⥤ Type) : P.Elements ⥤ P.Elements where
  obj T := P.elementsMk (T.obj.cont ℤ_[l]) (P.map (T.obj.toCont ℤ_[l]) T.val)
  map {T T'} φ := Functor.Elements.homMk (contMap φ.hom ℤ_[l]) (by
    rw [← Functor.map_comp_apply, toCont_contMap, Functor.map_comp_apply, φ.map_val])
  map_id T := Functor.Elements.hom_ext (contMap_id T.obj)
  map_comp φ ψ := Functor.Elements.hom_ext (contMap_comp φ.hom ψ.hom)

def iota (P : PAlg l ⥤ Type) : 𝟭 P.Elements ⟶ Xi P where
  app T := Functor.Elements.homMk (T.obj.toCont ℤ_[l]) rfl
  naturality T T' φ := Functor.Elements.hom_ext (toCont_contMap φ.hom).symm

def gam (P : PAlg l ⥤ Type) : Xi P ⟶ Xi P where
  app T := Functor.Elements.homMk (contShift T.obj) (by
    change P.map (contShift T.obj) (P.map (T.obj.toCont ℤ_[l]) T.val) =
      P.map (T.obj.toCont ℤ_[l]) T.val
    rw [← Functor.map_comp_apply, toCont_shift])
  naturality T T' φ := Functor.Elements.hom_ext (contMap_shift φ.hom)

def eta₀ (ε : Eps l) : (((base l).cont ℤ_[l]).A)ˣ := (GlobalTheory.T.continuous_algebra_universal_property ε).choose

theorem eta₀_sharp (ε : Eps l) : ((base l).cont ℤ_[l]).sharp (eta₀ ε) = 1 :=
  (GlobalTheory.T.continuous_algebra_universal_property ε).choose_spec.1

theorem eta₀_shift (ε : Eps l) :
    PAlg.Hom.f (contShift (base l)) (eta₀ ε) = ((base l).cont ℤ_[l]).s (ε.e 0) * eta₀ ε :=
  (GlobalTheory.T.continuous_algebra_universal_property ε).choose_spec.2.1

theorem eta₀_univ (ε : Eps l) (A t : PAlg l) (ht : t.IsTest) (φ : A ⟶ t) (u : (t.A)ˣ) (hu : t.sharp u = 1) :
    ∃! ψ : A.cont ℤ_[l] ⟶ t, A.toCont ℤ_[l] ≫ ψ = φ ∧
      PAlg.Hom.f ψ (PAlg.Hom.f (contMap A.fromBase ℤ_[l]) (eta₀ ε)) = u :=
  (GlobalTheory.T.continuous_algebra_universal_property ε).choose_spec.2.2 A t ht φ u hu

def eta (ε : Eps l) (A : PAlg l) : ((A.cont ℤ_[l]).A)ˣ :=
  Units.map (PAlg.Hom.f (contMap A.fromBase ℤ_[l])).toMonoidHom (eta₀ ε)

theorem eta_val (ε : Eps l) (A : PAlg l) :
    ((eta ε A : ((A.cont ℤ_[l]).A)ˣ) : (A.cont ℤ_[l]).A) = PAlg.Hom.f (contMap A.fromBase ℤ_[l]) (eta₀ ε) := rfl

theorem eta_sharp (ε : Eps l) (A : PAlg l) : (A.cont ℤ_[l]).sharp (eta ε A) = 1 := by
  rw [eta_val, ← mapU_sharp, eta₀_sharp, map_one]

theorem eta_map (ε : Eps l) {A B : PAlg l} (φ : A ⟶ B) :
    PAlg.Hom.f (contMap φ ℤ_[l]) (eta ε A) = eta ε B := by
  rw [eta_val, eta_val, ← fromBase_comp A φ, contMap_comp]
  rfl

theorem eta_shift (ε : Eps l) (A : PAlg l) :
    PAlg.Hom.f (contShift A) (eta ε A) = (A.cont ℤ_[l]).s (ε.e 0) * eta ε A := by
  have h : PAlg.Hom.f (contShift A) (PAlg.Hom.f (contMap A.fromBase ℤ_[l]) (eta₀ ε)) =
      PAlg.Hom.f (contMap A.fromBase ℤ_[l]) (PAlg.Hom.f (contShift (base l)) (eta₀ ε)) :=
    congrArg (fun f => PAlg.Hom.f f (eta₀ ε)) (contMap_shift A.fromBase).symm ▸ rfl
  rw [eta_val, h, eta₀_shift, map_mul]
  exact congrArg (· * _) (RingHom.congr_fun (Hom.comm (contMap A.fromBase ℤ_[l])) (ε.e 0 : Ob l))

def line (ε : Eps l) (P : PAlg l ⥤ Type) : Line (jE P) (epsU ε P) where
  Ξ := Xi P
  i := iota P
  η T := ⟨eta ε T.obj, MonoidHom.mem_ker.2 (Units.ext (eta_sharp ε T.obj))⟩
  map_η φ := Subtype.ext (Units.ext (eta_map ε φ.hom))
  γ := gam P
  iγ := NatTrans.ext (funext fun T => Functor.Elements.hom_ext (toCont_shift T.obj))
  γη T := Subtype.ext (Units.ext (eta_shift ε T.obj))
  univ T t φ a := by
    have ha : t.obj.obj.sharp (a.1).1 = 1 := congrArg Units.val (MonoidHom.mem_ker.1 a.2)
    obtain ⟨ψ, ⟨h1, h2⟩, hu⟩ := eta₀_univ ε T.obj t.obj.obj t.obj.property φ.hom a.1 ha
    have hψ : P.map ψ (P.map (T.obj.toCont ℤ_[l]) T.val) = t.val := by
      rw [← Functor.map_comp_apply, h1]
      exact φ.map_val
    refine ⟨Functor.Elements.homMk ψ hψ, ⟨Functor.Elements.hom_ext h1, Subtype.ext (Units.ext h2)⟩, ?_⟩
    rintro ⟨ψ', h'⟩ ⟨e1, e2⟩
    refine Functor.Elements.hom_ext (hu ψ' ⟨congrArg Functor.Elements.Hom.hom e1, ?_⟩)
    exact congrArg (fun x => (x.1).1) e2

theorem acr_ev_const (A : PAlg l) (n : ℕ) (z : ℤ_[l]) (a : A.Acr n) :
    mapAcr (A.evCont z) n (mapAcr (A.toCont ℤ_[l]) n a) = a := by
  rw [← mapAcr_comp, toCont_ev, mapAcr_id]

theorem acr_ev_shift (A : PAlg l) (n : ℕ) (z : ℤ_[l]) (x : (A.cont ℤ_[l]).Acr n) :
    mapAcr (A.evCont z) n (mapAcr (contShift A) n x) = mapAcr (A.evCont (z + 1)) n x := by
  rw [← mapAcr_comp, shift_ev]

theorem acr_toCont_injective (A : PAlg l) (n : ℕ) : Function.Injective (mapAcr (A.toCont ℤ_[l]) n) :=
  Function.LeftInverse.injective (g := mapAcr (A.evCont 0) n) (acr_ev_const A n 0)

theorem map_mem_map {A B : PAlg l} (f : A ⟶ B) (n : ℕ) (𝔞 : Ideal ((base l).Acr n)) {x : A.Acr n}
    (hx : x ∈ 𝔞.map (mapAcr A.fromBase n)) : mapAcr f n x ∈ 𝔞.map (mapAcr B.fromBase n) := by
  have h : 𝔞.map (mapAcr A.fromBase n) ≤ (𝔞.map (mapAcr B.fromBase n)).comap (mapAcr f n) :=
    Ideal.map_le_iff_le_comap.2 fun a ha => by
      rw [Ideal.mem_comap, Ideal.mem_comap, mapAcr_fromBase]
      exact Ideal.mem_map_of_mem _ ha
  exact h hx

theorem fixed_const (A : PAlg l) (n : ℕ) (𝔞 : Ideal ((base l).Acr n)) {x : (A.cont ℤ_[l]).Acr n}
    (hx : x ∈ 𝔞.map (mapAcr (A.cont ℤ_[l]).fromBase n)) (hg : mapAcr (contShift A) n x = x) :
    ∃ m ∈ 𝔞.map (mapAcr A.fromBase n), mapAcr (A.toCont ℤ_[l]) n m = x := by
  obtain ⟨hlc, hinj, -⟩ := _root_.GlobalTheory.CompanionTheory.ContAcr.acr_cont A n
  have hper : ∀ z, mapAcr (A.evCont z) n x = mapAcr (A.evCont 0) n x :=
    GlobalTheory.CompanionTheory.PadicShift.eq_of_shift_invariant l _ (hlc x) fun z => by
      rw [← acr_ev_shift, hg]
  refine ⟨mapAcr (A.evCont 0) n x, map_mem_map _ n 𝔞 hx, ?_⟩
  rw [← sub_eq_zero]
  refine hinj _ fun z => ?_
  rw [map_sub, acr_ev_const, hper z, sub_self]

theorem shift_surj (A : PAlg l) (n : ℕ) (𝔞 : Ideal ((base l).Acr n)) {x : (A.cont ℤ_[l]).Acr n}
    (hx : x ∈ 𝔞.map (mapAcr (A.cont ℤ_[l]).fromBase n)) :
    ∃ y ∈ 𝔞.map (mapAcr (A.cont ℤ_[l]).fromBase n), mapAcr (contShift A) n y - y = x := by
  obtain ⟨hlc, hinj, hex⟩ := _root_.GlobalTheory.CompanionTheory.ContAcr.acr_cont A n
  let f : ℤ_[l] → ↥(𝔞.map (mapAcr A.fromBase n)) := fun z =>
    ⟨mapAcr (A.evCont z) n x, map_mem_map _ n 𝔞 hx⟩
  have hf : IsLocallyConstant f := by
    refine (IsLocallyConstant.iff_eventually_eq f).2 fun z => ?_
    filter_upwards [(IsLocallyConstant.iff_eventually_eq _).1 (hlc x) z] with w hw
    exact Subtype.ext hw
  have hN : ∀ a : ↥(𝔞.map (mapAcr A.fromBase n)), l ^ n • a = 0 := fun a => Subtype.ext (by
    change l ^ n • (a.1 : A.Acr n) = 0
    rw [nsmul_eq_mul, Nat.cast_pow, A.pow_l_acr n, zero_mul])
  obtain ⟨y, hy, hd⟩ := GlobalTheory.CompanionTheory.PadicShift.exists_primitive l n hN f hf
  obtain ⟨w, hw, hwz⟩ := hex 𝔞 (fun z => (y z).1) (hy.comp _) fun z => (y z).2
  refine ⟨w, hw, ?_⟩
  rw [← sub_eq_zero]
  refine hinj _ fun z => ?_
  rw [map_sub, map_sub, acr_ev_shift, hwz, hwz, sub_eq_zero]
  exact congrArg Subtype.val (hd z)

theorem facyc_of {R : Type} [CommRing R] {C : Type*} [Category C] {G : C ⥤ ModuleCat.{0} R} (Φ : Flt G) {T T' : C}
    (i : T ⟶ T') (g : T' ⟶ T') (h1 : Function.Injective (G.map i).hom)
    (h2 : ∀ r, ∀ x ∈ (Φ.S r).S T', (G.map g).hom x = x → ∃ m, m ∈ (Φ.S r).S T ∧ (G.map i).hom m = x)
    (h3 : ∀ r, ∀ x ∈ (Φ.S r).S T', ∃ y, y ∈ (Φ.S r).S T' ∧ (G.map g).hom y - y = x) : Φ.FAcyc i g := by
  refine ⟨h1, fun r x hx hg => ?_, fun r x hx => ?_⟩
  · obtain ⟨m, hm, hmx⟩ := h2 r x hx hg
    exact ⟨_, Φ.mul r T m hm, by rw [map_smul, hmx]⟩
  · obtain ⟨y, hy, hyx⟩ := h3 r x hx
    exact ⟨_, Φ.mul r T' y hy, by rw [map_smul, ← smul_sub, hyx]⟩

section Main

variable {O : Type} [CommRing O] (F : Fn O) (κ : O →+* OC l) (ε : Eps l) (k : Bool) (n : ℕ) (ρ : ℕ → ℕ) (hρ : Slow ρ)

theorem mem_step (r : ℕ) (T : (F.pt κ).Elements) (x : T.1.Acr n) :
    x ∈ (((flt F κ ε k n ρ hρ).comap (gE F κ k n)).S r).S T ↔
      x ∈ (fil (DD k (base l) n) (ρ r)).map (mapAcr T.1.fromBase n) := by
  rw [← (_root_.GlobalTheory.CompanionTheory.AcrMod.acr_modp T.1 n).2.2.2.2.1 k (ρ r)]
  rfl

theorem step_fixed (T : (F.pt κ).Elements) (r : ℕ) (x : (T.1.cont ℤ_[l]).Acr n)
    (hx : x ∈ (((flt F κ ε k n ρ hρ).comap (gE F κ k n)).S r).S ((Xi (F.pt κ)).obj T))
    (hg : mapAcr (contShift T.1) n x = x) :
    ∃ m : T.1.Acr n, m ∈ (((flt F κ ε k n ρ hρ).comap (gE F κ k n)).S r).S T ∧
      mapAcr (T.1.toCont ℤ_[l]) n m = x := by
  obtain ⟨m, hm, hmx⟩ := fixed_const T.1 n _ ((mem_step F κ ε k n ρ hρ r ((Xi (F.pt κ)).obj T) x).1 hx) hg
  exact ⟨m, (mem_step F κ ε k n ρ hρ r T m).2 hm, hmx⟩

theorem step_surj (T : (F.pt κ).Elements) (r : ℕ) (x : (T.1.cont ℤ_[l]).Acr n)
    (hx : x ∈ (((flt F κ ε k n ρ hρ).comap (gE F κ k n)).S r).S ((Xi (F.pt κ)).obj T)) :
    ∃ y : (T.1.cont ℤ_[l]).Acr n, y ∈ (((flt F κ ε k n ρ hρ).comap (gE F κ k n)).S r).S ((Xi (F.pt κ)).obj T) ∧
      mapAcr (contShift T.1) n y - y = x := by
  obtain ⟨y, hy, hyx⟩ := shift_surj T.1 n _ ((mem_step F κ ε k n ρ hρ r ((Xi (F.pt κ)).obj T) x).1 hx)
  exact ⟨y, (mem_step F κ ε k n ρ hρ r ((Xi (F.pt κ)).obj T) y).2 hy, hyx⟩

theorem facyc (T : (F.pt κ).Elements) :
    ((flt F κ ε k n ρ hρ).comap (gE F κ k n)).FAcyc ((line ε (F.pt κ)).i.app T) ((line ε (F.pt κ)).γ.app T) :=
  facyc_of _ _ _ (acr_toCont_injective T.1 n) (fun r x hx hg => step_fixed F κ ε k n ρ hρ T r x hx hg)
    (fun r x hx => step_surj F κ ε k n ρ hρ T r x hx)

end Main

theorem exists_line : ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] (F : Fn O) (κ : O →+* OC l) (ε : Eps l) (k : Bool) (n : ℕ) (ρ : ℕ → ℕ) (hρ : Slow ρ), ∃ L : Line (jE (F.pt κ)) (epsU ε (F.pt κ)), ∀ T, ((flt F κ ε k n ρ hρ).comap (gE F κ k n)).FAcyc (L.i.app T) (L.γ.app T) :=
  fun F κ ε k n ρ hρ => ⟨line ε (F.pt κ), facyc F κ ε k n ρ hρ⟩

end GlobalTheory.CompanionTheory.ContLine
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AcrisIsAdicComplete
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits AlgebraicGeometry TensorProduct GroundTheory.PAdicHodge GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison.PAlg CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.ACrisAdic

theorem acris_isAdicComplete :
    ∀ {l : ℕ} [Fact l.Prime], IsAdicComplete (Ideal.span {(l : Acris l)}) (Acris l) := by
  intro l _
  exact ACris.isAdicComplete ℂ_[l] l

end GlobalTheory.CompanionTheory.ACrisAdic
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdmissibleUnitarySemisimple
section
open GlobalTheory.PRep GlobalTheory.SmGL
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.UnitSemisimple

variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem exists_proj_finset (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ)
    (hp : ∀ v, v ≠ 0 → 0 < (B v v).re) (t : Finset V) :
    ∀ v : V, ∃ w ∈ Submodule.span ℂ (t : Set V),
      ∀ s ∈ Submodule.span ℂ (t : Set V), B (v - w) s = 0 := by
  classical
  induction t using Finset.induction_on with
  | empty =>
    intro v
    refine ⟨0, zero_mem _, fun s hs => ?_⟩
    have : s = 0 := by simpa using hs
    simp [this]
  | insert a t _ ih =>
    intro v
    obtain ⟨w₁, hw₁, h₁⟩ := ih v
    obtain ⟨a₁, ha₁, h₂⟩ := ih a
    have hle : Submodule.span ℂ (t : Set V) ≤ Submodule.span ℂ ((insert a t : Finset V) : Set V) :=
      Submodule.span_mono (by simp)
    have ha : a ∈ Submodule.span ℂ ((insert a t : Finset V) : Set V) :=
      Submodule.subset_span (by simp)
    obtain ⟨x, hx⟩ : ∃ x, x = a - a₁ := ⟨_, rfl⟩
    obtain ⟨u, hu⟩ : ∃ u, u = v - w₁ := ⟨_, rfl⟩
    obtain ⟨c, hcdef⟩ : ∃ c, c = B u x / B x x := ⟨_, rfl⟩
    have hc : B u x = c * B x x := by
      by_cases hx0 : x = 0
      · simp [hx0]
      · have h0 : B x x ≠ 0 := fun h => by simpa [h] using hp x hx0
        rw [hcdef]; field_simp
    refine ⟨w₁ + c • x, ?_, ?_⟩
    · refine add_mem (hle hw₁) (Submodule.smul_mem _ _ ?_)
      rw [hx]; exact sub_mem ha (hle ha₁)
    · intro s hs
      rw [Finset.coe_insert] at hs
      obtain ⟨b, z, hz, rfl⟩ := Submodule.mem_span_insert.1 hs
      have hz' : b • a₁ + z ∈ Submodule.span ℂ (t : Set V) :=
        add_mem (Submodule.smul_mem _ _ ha₁) hz
      have e1 : v - (w₁ + c • x) = u - c • x := by rw [hu]; abel
      have e2 : b • a + z = b • x + (b • a₁ + z) := by rw [hx, smul_sub]; abel
      have k1 : B u (b • a₁ + z) = 0 := by rw [hu]; exact h₁ _ hz'
      have k2 : B x (b • a₁ + z) = 0 := by rw [hx]; exact h₂ _ hz'
      rw [e1, e2, map_sub, LinearMap.sub_apply, map_smul, LinearMap.smul_apply,
        (B u).map_add (b • x), (B x).map_add (b • x),
        k1, k2, LinearMap.map_smulₛₗ, LinearMap.map_smulₛₗ, hc]
      simp only [smul_eq_mul, add_zero]
      ring

theorem mem_fixed_iff {G : Type} [Group G] (ρ : Representation ℂ G V) (K : Subgroup G) (v : V) :
    v ∈ fixed ρ K ↔ ∀ k ∈ K, ρ k v = v := by
  constructor
  · intro h k hk
    simpa using h ⟨k, hk⟩
  · intro h k
    simpa using h k k.2

theorem orbit_finite {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (ρ : Representation ℂ G V) (K : Subgroup G) (hK : IsCompact (K : Set G)) (w : V)
    (hS : IsOpen {g : G | ρ g w = w}) : {x : V | ∃ k ∈ K, ρ k w = x}.Finite :=
  _root_.UpperTheory.Reformulated.B.Qf32.orbit_finite ρ K hK w hS

theorem orthogonal_of_fixed {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (ρ : Representation ℂ G V) (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ)
    (hi : ∀ g v w, B (ρ g v) (ρ g w) = B v w) (K : Subgroup G) (hK : IsCompact (K : Set G))
    (W : Subrepresentation ρ) (u : V) (hu : ∀ k ∈ K, ρ k u = u)
    (huW : ∀ s ∈ W.toSubmodule ⊓ fixed ρ K, B u s = 0)
    (w : V) (hw : w ∈ W.toSubmodule) (hS : IsOpen {g : G | ρ g w = w}) : B u w = 0 := by
  classical
  have hO := orbit_finite ρ K hK w hS
  set O : Finset V := hO.toFinset with hOdef
  have hmem : ∀ x, x ∈ O ↔ ∃ k ∈ K, ρ k w = x := fun x => by simp [hOdef]
  have hinv : ∀ k ∈ K, ∀ x, ρ k⁻¹ (ρ k x) = x := fun k _ x => by
    rw [← Module.End.mul_apply, ← map_mul]; simp
  have hinv' : ∀ k ∈ K, ∀ x, ρ k (ρ k⁻¹ x) = x := fun k _ x => by
    rw [← Module.End.mul_apply, ← map_mul]; simp
  have hst : ∀ k ∈ K, ∀ x ∈ O, ρ k x ∈ O := by
    intro k hk x hx
    obtain ⟨l, hl, rfl⟩ := (hmem x).1 hx
    refine (hmem _).2 ⟨k * l, K.mul_mem hk hl, ?_⟩
    rw [map_mul, Module.End.mul_apply]
  have hsW : ∑ x ∈ O, x ∈ W.toSubmodule := by
    refine Submodule.sum_mem _ fun x hx => ?_
    obtain ⟨l, _, rfl⟩ := (hmem x).1 hx
    exact W.apply_mem_toSubmodule l hw
  have hsF : ∑ x ∈ O, x ∈ fixed ρ K := by
    rw [mem_fixed_iff]
    intro k hk
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    exact Finset.sum_nbij' (ρ k) (ρ k⁻¹) (fun x hx => hst k hk x hx)
      (fun x hx => hst _ (K.inv_mem hk) x hx) (fun x _ => hinv k hk x) (fun x _ => hinv' k hk x)
      (fun x _ => rfl)
  have h0 := huW _ ⟨hsW, hsF⟩
  have hterm : ∀ x ∈ O, B u x = B u w := by
    intro x hx
    obtain ⟨l, hl, rfl⟩ := (hmem x).1 hx
    conv_lhs => rw [← hu l hl]
    exact hi l u w
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, Finset.sum_congr rfl hterm, Finset.sum_const] at h0
  have hne : O.card ≠ 0 := Finset.card_ne_zero.2 ⟨w, (hmem w).2 ⟨1, K.one_mem, by simp⟩⟩
  rw [nsmul_eq_mul] at h0
  exact (mul_eq_zero.1 h0).resolve_left (by exact_mod_cast hne)

def orth {G : Type} [Group G] (ρ : Representation ℂ G V) (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ)
    (hi : ∀ g v w, B (ρ g v) (ρ g w) = B v w) (W : Subrepresentation ρ) : Subrepresentation ρ where
  toSubmodule :=
    { carrier := {v | ∀ w ∈ W.toSubmodule, B v w = 0}
      add_mem' := fun {a b} ha hb w hw => by simp [ha w hw, hb w hw]
      zero_mem' := fun w _ => by simp
      smul_mem' := fun c v hv w hw => by simp [hv w hw] }
  apply_mem_toSubmodule := by
    intro g v hv w hw
    have e : ρ g (ρ g⁻¹ w) = w := by
      rw [← Module.End.mul_apply, ← map_mul]; simp
    have := hv _ (W.apply_mem_toSubmodule g⁻¹ hw)
    rw [← e, hi]; exact this

theorem exists_isCompl : ∀ {G V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V), (∀ U ∈ nhds (1 : G), ∃ K : Subgroup G, IsOpen (K : Set G) ∧ IsCompact (K : Set G) ∧ (K : Set G) ⊆ U) → IsAdmissible ρ → IsUnitarisable ρ → ∀ W : Subrepresentation ρ, ∃ W' : Subrepresentation ρ, IsCompl W W' := by
  intro G V _ _ _ _ _ ρ hbasis hadm hun W
  obtain ⟨B, hh, hp, hi⟩ := hun
  refine ⟨orth ρ B hi W, IsCompl.of_eq ?_ ?_⟩
  · apply Subrepresentation.toSubmodule_injective
    rw [Subrepresentation.toSubmodule_inf]
    refine (Submodule.eq_bot_iff _).2 fun v hv => ?_
    by_contra hv0
    have h0 : B v v = 0 := hv.2 v hv.1
    simpa [h0] using hp v hv0
  · apply Subrepresentation.toSubmodule_injective
    rw [Subrepresentation.toSubmodule_sup]
    refine (Submodule.eq_top_iff').2 fun v => ?_
    obtain ⟨K, hKo, hKc, hKv⟩ := hbasis {g | ρ g v = v} ((hadm.1 v).mem_nhds (by simp))
    have hfd : FiniteDimensional ℂ (fixed ρ K) := hadm.2 K hKo hKc
    have hfd' : FiniteDimensional ℂ (W.toSubmodule ⊓ fixed ρ K : Submodule ℂ V) :=
      Submodule.finiteDimensional_inf_right _ _
    have hfg : (W.toSubmodule ⊓ fixed ρ K).FG := Module.Finite.iff_fg.1 hfd'
    obtain ⟨t, ht⟩ := hfg
    obtain ⟨w, hw, hort⟩ := exists_proj_finset B hp t v
    rw [ht] at hw hort
    have hfix : ∀ k ∈ K, ρ k (v - w) = v - w := by
      intro k hk
      have h1 : ρ k v = v := hKv hk
      have h2 : ρ k w = w := (mem_fixed_iff ρ K w).1 hw.2 k hk
      rw [map_sub, h1, h2]
    have hmem : v - w ∈ (orth ρ B hi W).toSubmodule := fun y hy =>
      orthogonal_of_fixed ρ B hi K hKc W (v - w) hfix hort y hy (hadm.1 y)
    have : v = w + (v - w) := by abel
    rw [this]
    exact Submodule.add_mem_sup hw.1 hmem

end GlobalTheory.CompanionTheory.UnitSemisimple
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AffineFinsetInf
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

noncomputable section

open CategoryTheory

namespace GlobalTheory.CompanionTheory.RelInjAbs

open CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Onto

section Cxs

variable {R : Type} [CommRing R]

end Cxs

section Abs

variable {R : Type} [CommRing R] {C C' : Type 1} [Category.{0} C] [Category.{0} C']
  {F : C ⥤ ModuleCat.{0} R} {F' : C' ⥤ ModuleCat.{0} R} (m : CH.Mor F F' (RingHom.id R))
  {ι : Type} [DecidableEq ι]

theorem bij_res_of_eq {Ut V₁ V₂ : ObjectProperty C} (e : V₁ = V₂) {Q : ObjectProperty C} (hQ : Cosieve Q) (h₁ : V₁ ≤ Ut)
    (h₂ : V₂ ≤ Ut) (n : ℕ) (hb : Function.Bijective ((RC.res F hQ h₁).mapH n)) :
    Function.Bijective ((RC.res F hQ h₂).mapH n) := by
  subst e
  exact hb

theorem capU_empty (U : ι → ObjectProperty C) : (fun T => ∃ α, U α T) = capU U ∅ := by
  funext T
  exact propext ⟨fun h => ⟨h, fun α hα => absurd hα (Finset.notMem_empty α)⟩, fun h => h.1⟩

theorem capU_nonempty (U : ι → ObjectProperty C) (P : ObjectProperty C) (S : Finset ι) (hS : S.Nonempty)
    (h : ∀ T, P T ↔ ∀ α ∈ S, U α T) : capU U S = P := by
  funext T
  refine propext ⟨fun hT => (h T).2 hT.2, fun hT => ?_⟩
  obtain ⟨α, hα⟩ := hS
  exact ⟨⟨α, (h T).1 hT α hα⟩, (h T).1 hT⟩

end Abs

end GlobalTheory.CompanionTheory.RelInjAbs

namespace GlobalTheory.CompanionTheory.RelInjZ

open _root_.CategoryTheory.Limits AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.HT CrystallineSemistableComparison.Onto GlobalTheory.CompanionTheory.RelInjAbs

variable {K : Type} [Field K] {W Z Y : Scheme.{0}} {q : Z ⟶ Spec (CommRingCat.of K)} {i : W ⟶ Z} {π : Y ⟶ Z}
  {D : E.LineData Y} {d : ℕ}

theorem affine_inf (q : Z ⟶ Spec (CommRingCat.of K)) [IsSeparated q] {V V' : Z.Opens} (h : IsAffineOpen V) (h' : IsAffineOpen V') :
    IsAffineOpen (V ⊓ V') :=
  GlobalTheory.FinNear.isAffineOpen_preimage_inf_of_isSeparated_over (𝟙 Z) q (isAffineOpen_top (Spec (CommRingCat.of K))) h
    (fun _ _ => trivial) h' (fun _ _ => trivial)

theorem affine_finset_inf (q : Z ⟶ Spec (CommRingCat.of K)) [IsSeparated q] {κ : Type} (V : κ → Z.Opens) (S : Finset κ)
    (hS : S.Nonempty) (h : ∀ o ∈ S, IsAffineOpen (V o)) : IsAffineOpen (S.inf V) := by
  classical
  induction S using Finset.induction_on with
  | empty => exact absurd hS Finset.not_nonempty_empty
  | insert a s ha ih =>
    rw [Finset.inf_insert]
    rcases s.eq_empty_or_nonempty with rfl | hs
    · simpa using h a (by simp)
    · exact affine_inf q (h a (by simp)) (ih hs fun o ho => h o (Finset.mem_insert_of_mem ho))

theorem inU_finset_inf (hs : SiteLaws) (i : W ⟶ Z) {κ : Type} (V : κ → Z.Opens) (S : Finset κ) (T) :
    inU q (S.inf V) T ↔ ∀ o ∈ S, inU q (V o) T := by
  classical
  obtain ⟨-, -, htop, hinf, -, -⟩ := hs K W Z Z q i (𝟙 Z)
  induction S using Finset.induction_on with
  | empty => simpa using htop T
  | insert a s ha ih =>
    rw [Finset.inf_insert, hinf, ih]
    simp

end GlobalTheory.CompanionTheory.RelInjZ
end
end

