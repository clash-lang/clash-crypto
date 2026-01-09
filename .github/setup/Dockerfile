FROM ubuntu:22.04

# What version of Attic to install
ARG ATTIC_VERSION="687dd7d607824edf11bf33e3d91038467e7fad43"
ARG NIX_BURN_IN_TARGETS=".#packages.x86_64-linux.ciEnv"

RUN \
  apt-get update && \
  apt-get install -y libftdi-dev curl xz-utils sudo git && \
  rm -rf /var/lib/apt/lists/*

RUN \
  groupadd -r nixbld && \
  for n in $(seq 1 10); do \
    useradd \
      -c "Nix build user $n"\
      -d /var/empty \
      -g nixbld \
      -G nixbld \
      -M -N -r \
      -s "$(command -v nologin)" "nixbld$n";\
  done && \
  curl -L https://nixos.org/nix/install --output install_nix.sh && \
  sh install_nix.sh

ENV \
  NIX_SSL_CERT_FILE=/etc/ssl/certs/ca-certificates.crt \
  MANPATH="/root/.nix-profile/share/man" \
  PATH="/root/.nix-profile/bin:$PATH"

# Add config
RUN mkdir /etc/nix && echo '\
build-users-group = nixbld \n\
sandbox = false \n\
cores = 0 \n\
max-jobs = auto \n\
experimental-features = nix-command flakes ca-derivations \n\
substituters = https://cache.nixos.org/ http://192.168.102.136:9200/public/ \n\
trusted-substituters = http://192.168.102.136:9200/public/ \n\
trusted-public-keys = cache.nixos.org-1:6NCHdD59X431o0gWypbMrAURkbJ16ZPMQFGspcDShjY= public:PGGlJMx1gGmU069blMqve8tS1ndzBuriUAwGBHGOo4g= \n\
' > /etc/nix/nix.conf

# Burn in the requested targets from this repository
COPY flake.nix flake.lock nix /burn-in-env/
RUN \
  cd /burn-in-env && \
  nix build ${NIX_BURN_IN_TARGETS} && \
  cd / && \
  rm -rf /burn-in-env

# fix the known github.com host keys
RUN mkdir ~/.ssh && echo '\
github.com ssh-ed25519 AAAAC3NzaC1lZDI1NTE5AAAAIOMqqnkVzrm0SdG6UOoqKLsabgH5C9okWi0dh2l9GKJl\n\
github.com ecdsa-sha2-nistp256 AAAAE2VjZHNhLXNoYTItbmlzdHAyNTYAAAAIbmlzdHAyNTYAAABBBEmKSENjQEezOmxkZMy7opKgwFB9nkt5YRrYMjNuG5N87uRgg6CLrbo5wAdT/y6v0mKV0U2w0WZ2YB/++Tpockg=\n\
github.com ssh-rsa AAAAB3NzaC1yc2EAAAADAQABAAABgQCj7ndNxQowgcQnjshcLrqPEiiphnt+VTTvDP6mHBL9j1aNUkY4Ue1gvwnGLVlOhGeYrnZaMgRK6+PKCUXaDbC7qtbW8gIkhL7aGCsOr/C56SJMy/BCZfxd1nWzAOxSDPgVsmerOBYfNqltV9/hWCqBywINIR+5dIg6JTJ72pcEpEjcYgXkE2YEFXV1JHnsKgbLWNlhScqb2UmyRkQyytRLtL+38TGxkxCflmO+5Z8CSSNY7GidjMIZ7Q4zMjA2n1nGrlTDkzwDCsw+wqFPGQA179cnfGWOWRVruj16z6XyvxvjJwbz0wQZ75XK5tKSb7FNyeIEs4TT4jk+S4dhPeAUC5y+bDYirYgM4GC7uEnztnZyaVWQ7B381AK4Qdrwt51ZqExKbQpTUNn+EjqoTwvqNj4kqx5QUCI0ThS/YkOxJCXmPUWZbhjpCg56i+2aB6CmK2JGhn57K5mj0MNdBXA4/WnwH6XoPWJzK5Nyu2zB3nAZp+S5hpQs+p1vN1/wsjk=\n\
' > ~/.ssh/known_hosts

# Install the deploykey script
COPY .github/setup/deploykey /usr/bin/deploykey
RUN chmod 711 /usr/bin/deploykey

# Install attic (Nix binary cache)
RUN nix profile add github:zhaofengli/attic?rev=${ATTIC_VERSION}#packages.x86_64-linux.attic
