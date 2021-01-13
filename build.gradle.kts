/*
 * Copyright 2020 TU Dortmund, Malte Mues
 */
import org.gradle.api.tasks.testing.logging.TestLogEvent.*

plugins {
    `antlr`
    `java-library`
    `java`
    `maven-publish`
    id("com.github.hierynomus.license") version "0.15.0"
    id("com.github.johnrengelman.shadow") version "5.2.0"
    id("com.github.sherter.google-java-format") version "0.9"
}

java {
    toolchain {
        languageVersion.set(JavaLanguageVersion.of(8))
    }
}

group = "tools.aqua"
version = "0.9.6-SNAPSHOT"

repositories {
    mavenCentral()
    maven { url = uri("https://jitpack.io") }
}

dependencies {
    antlr("org.antlr:antlr:3.5.2")
    implementation("com.google.guava:guava:14.0.1")
    implementation("com.github.tudo-aqua:jSMTLIB:5c11ee5")
    implementation("commons-cli:commons-cli:1.4")
    implementation("dk.brics:automaton:1.12-1")
    implementation("org.antlr:antlr-runtime:3.5.2")
    implementation("org.apache.commons:commons-math3:3.6.1")
    testImplementation("org.testng:testng:6.8")
}

group = "tools.aqua"
version = "0.9.6-SNAPSHOT"
description = "jConstraints"

license {
    header = file("NOTICE")
    excludes(setOf("**/*.smt2", "**/*.txt"))
}

tasks.test {
    useTestNG() {
        useDefaultListeners = true
        includeGroups = setOf("base")
    }
    testLogging {
        events(FAILED, STANDARD_ERROR, SKIPPED, PASSED)
    }
}

tasks.shadowJar.configure{
    archiveFileName.set("${baseName}-${classifier}-${version}.jar")
}

publishing {
    publications {
        create<MavenPublication>("mavenJava") {
            artifactId = "jconstraints"
            from(components["java"])
            pom {
                name.set("jConstraints")
                description.set("jConstraints is a library for managing SMT constraints in Java.")
                url.set("https://github.com/tudo-aqua/jconstraints")
                licenses {
                    license {
                        name.set("Apache-2.0")
                        url.set("https://www.apache.org/licenses/LICENSE-2.0.txt")
                    }
                }
                developers {
                    developer {
                        id.set("mmuesly")
                        name.set("Malte Mues")
                        email.set("mail.mues@gmail.com")
                    }
                    developer {
                        id.set("fhowar")
                        name.set("Falk Howar")
                    }
                }
                scm {
                    connection.set("https://github.com/tudo-aqua/jconstraints.git")
                    url.set("https://github.com/tudo-aqua/jconstraints")
                }
            }
        }
        create<MavenPublication>("publishMaven") {
            artifact(tasks["shadowJar"]){
                classifier = null
            }
            artifactId = "jconstraints-all"

        }
    }
}
