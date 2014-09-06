MRuby::Gem::Specification.new('mruby-gmp-bignum') do |spec|
  spec.license = 'MIT'
  spec.author  = 'Ray Chason'
  spec.summary = 'GMP-based Bignum implementation'
  spec.linker.libraries << 'gmp'
end
